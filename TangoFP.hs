{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
module TangoFP where
import Control.Applicative ( liftA2, empty ) -- base
import Control.Concurrent.STM.TVar ( TVar, newTVarIO, readTVar, readTVarIO, writeTVar, modifyTVar' ) -- stm
import Control.Monad ( when ) -- base
import Control.Monad.STM ( STM, atomically ) -- stm
import qualified Data.ByteString.Lazy as LBS -- bytestring
import Data.Char ( isDigit, isSpace, digitToInt ) -- base
import Data.Dynamic ( Typeable, toDyn, fromDynamic, Dynamic ) -- base
import Data.Foldable ( all, and, maximum, notElem, forM_, mapM_, toList ) -- base
import Data.Functor ( ($>) ) -- base
import qualified Data.IntMap as IM -- containers
import Data.IORef ( IORef, newIORef, atomicModifyIORef', modifyIORef', readIORef, writeIORef ) -- base
import Data.List ( isSuffixOf ) -- base
import qualified Data.Map as M -- containers
import qualified Data.Sequence as S -- containers
import Data.Traversable ( forM ) -- base
import GHC.Generics ( Generic ) -- base?
import System.Console.ANSI ( setSGR, Color(..), ColorIntensity(..), ConsoleIntensity(..), ConsoleLayer(..), SGR(..) ) -- ansi-terminal
import System.Directory ( getDirectoryContents ) -- directory
import System.IO ( FilePath ) -- base
import System.IO.Error ( ioError, userError ) -- base

import qualified Data.Csv as Csv -- cassava
import Data.Csv ( (.!) ) -- cassava

import Debug.Trace ( trace ) -- base

print' :: (Show a) => String -> a -> IO ()
print' prompt x = putStr (prompt ++ ": ") >> print x

-- Log ----------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

data Log a = Log { 
    logRead :: Position -> IO (Maybe a),
    logAppend :: a -> IO Position,
    logLatestPosition :: IO Position,
    logCursorFrom :: Position -> IO (Cursor a),
    logCursorFromTo :: Position -> Position -> IO (Cursor a),
    subscribeToLog :: (Position -> a -> IO ()) -> IO (IO ())
  }

type Position = Int

type Cursor a = IO (Maybe (Position, a))

makeInMemoryLog :: IO (Log a)
makeInMemoryLog = makeInMemoryLog' []

makeInMemoryLog' :: [a] -> IO (Log a)
makeInMemoryLog' xs = do
    (logVar, observersRef) <- liftA2 (,) (newTVarIO (S.fromList xs)) (newIORef [])
    return $ Log {
        logRead = \ix -> do
            s <- readTVarIO logVar
            if ix < S.length s then return $ Just (s `S.index` ix) else return Nothing,
            
        logAppend = \ x -> do
            len <- atomically $ do
                    s <- readTVar logVar
                    let !len = S.length s
                    writeTVar logVar (s S.|> x)
                    return len
            mapM_ (\action -> action len x) =<< readIORef observersRef
            return len,

        logLatestPosition = S.length <$> readTVarIO logVar,

        logCursorFrom = \ix -> do
            cursorRef <- readTVarIO logVar >>= newIORef . (,) ix . S.drop ix
            return $ atomicModifyIORef' cursorRef (\c@(ix, s) -> case S.viewl s of S.EmptyL -> (c, Nothing); x S.:< xs -> let !ix' = ix + 1 in ((ix', xs), Just (ix, x))),

        logCursorFromTo = \ix stopIx -> do
            cursorRef <- readTVarIO logVar >>= newIORef . (,) ix . S.drop ix . S.take (stopIx + 1)
            return $ atomicModifyIORef' cursorRef (\c@(ix, s) -> case S.viewl s of S.EmptyL -> (c, Nothing); x S.:< xs -> let !ix' = ix + 1 in ((ix', xs), Just (ix, x))),

        subscribeToLog = \observer -> do
            modifyIORef' observersRef (observer:)
            return (return ()) -- TODO: Actually implement returned unsubscribe action.
    }

printLog :: (Show a) => Log a -> IO ()
printLog (Log { logCursorFrom = logCursorFrom }) = do
    cursor <- logCursorFrom 0
    let go = maybe (return ()) (\x -> print x >> go) =<< cursor
    go

-- Tango Specification ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

-- Preconditions:
--  * The positions are within the log
--  * The OIDs in the read sets match the OIDs of the entries they point to
--  * The OIDs are unique in the read sets (both passed in ones and ones from commit entries)
--  * The OIDs are unique in the write set (i.e. the OIDs of the entries the write sets point at)
--  * The read set positions precede the passed in stop position.
--  * Positions in read and write sets in commit entries refer to earlier log positions.
--  * All positions are >= 0 (except for the passed in readSet positions)
checkCommitSpecification :: Log (TangoEntry a) -> [(OID, Position)] -> Position -> IO Bool
checkCommitSpecification log [] stopPosition = return True
checkCommitSpecification log readSet stopPosition = do
    let readSetMap = IM.fromList readSet
    let checkOID oid pos = case IM.lookup oid readSetMap of
                            Just p | p < pos -> False
                            _ -> True
    let go pos | pos >= stopPosition = return True
        go pos = do
            Just entry <- logRead log pos
            case entry of
                AbortEntry {} -> go (pos+1)
                UpdateEntry { speculativeFlag = True } -> go (pos+1)
                UpdateEntry { oid = oid } | checkOID oid pos -> go (pos+1)
                                          | otherwise -> return False
                CommitEntry { readSet = readSet, writeSet = writeSet } -> do
                    committed <- checkCommitSpecification log readSet pos
                    if committed then do
                        writes <- mapM (logRead log) writeSet
                        if all (\(Just (UpdateEntry { oid = oid })) -> checkOID oid pos) writes then go (pos+1) else return False
                      else go (pos+1)
    go (minimum (map snd readSet))                

-- Preconditions:
--  * The positions are within the log
--  * The OIDs in the read sets match the OIDs of the entries they point to
--  * The OIDs are unique in the read sets (both passed in ones and ones from commit entries)
--  * The OIDs are unique in the write set (i.e. the OIDs of the entries the write sets point at)
--  * The read set positions precede the passed in stop position.
--  * Positions in read and write sets in commit entries refer to earlier log positions.
--  * All positions are >= 0 (except for the passed in readSet positions)
pureCheckCommitSpecification :: S.Seq (TangoEntry a) -> [(OID, Position)] -> Position -> Bool
pureCheckCommitSpecification log [] stopPosition = True
pureCheckCommitSpecification log readSet stopPosition = go (max 0 (minimum (map snd readSet)))
    where readSetMap = IM.fromList readSet
          checkOID oid pos = case IM.lookup oid readSetMap of
                                Just p | p < pos -> False
                                _ -> True
          go pos | pos >= stopPosition = True
          go pos = 
            let entry = S.index log pos
            in case entry of
                  AbortEntry {} -> go (pos+1)
                  UpdateEntry { speculativeFlag = True } -> go (pos+1)
                  UpdateEntry { oid = oid } | checkOID oid pos -> go (pos+1)
                                            | otherwise -> False
                  CommitEntry { readSet = readSet, writeSet = writeSet } -> 
                      let committed = pureCheckCommitSpecification log readSet pos
                      in if not committed || all (\(UpdateEntry { oid = oid }) -> checkOID oid pos) (map (S.index log) writeSet) then go (pos+1) else False

-- Ignores the expectedResult and commitSucceeded fields and populates them with the correct data.
traceExecutorSpecification :: [TraceOp Int] -> [TraceOp Int]
traceExecutorSpecification = go [] S.empty M.empty IM.empty IM.empty
    where go !acc !_ !_ !_ !_ [] = reverse acc

          go acc log values writeSets readSets (TraceRead { traceRuntimeId = Nothing, traceOID = oid }:ops) = 
            go (TraceRead Nothing oid (fst $ M.findWithDefault (0, undefined) (Nothing, oid) values):acc) log values writeSets readSets ops

          go acc log values writeSets readSets (TraceRead { traceRuntimeId = Just rtId, traceOID = oid }:ops) = 
            let combineIfNew [(oid, pos)] old = if any (\(oid', _) -> oid' == oid) old then old else (oid,pos):old
                (value, version) = maybe (M.findWithDefault (0, -1) (Nothing, oid) values) id (M.lookup (Just rtId, oid) values)
            in go (TraceRead (Just rtId) oid value:acc) log values writeSets (IM.insertWith combineIfNew rtId [(oid, version)] readSets) ops

          go acc log values writeSets readSets (op@(TraceWrite { traceRuntimeId = Nothing, traceOID = oid, valueToWrite = val }):ops) =
            go (op:acc) (log S.|> UpdateEntry False True oid val) (M.insert (Nothing, oid) (val, S.length log) values) writeSets readSets ops

          go acc log values writeSets readSets (op@(TraceWrite { traceRuntimeId = Just rtId, traceOID = oid, valueToWrite = val }):ops) =
            go (op:acc) (log S.|> UpdateEntry True True oid val) (M.insert (Just rtId, oid) (val, S.length log) values) (IM.insertWith (++) rtId [S.length log] writeSets) readSets ops

          go acc log values writeSets readSets (TraceCommit { traceTransactionId = trtId }:ops) = 
            let writeSet = IM.findWithDefault [] trtId writeSets
                readSet = IM.findWithDefault [] trtId readSets
                pos = S.length log
                committed = pureCheckCommitSpecification log readSet (if null writeSet then maximum (map snd readSet) else pos)
                values' = if committed then 
                            M.fromListWith (\_ x -> x) (map (\p -> case S.index log p of UpdateEntry _ _ oid val -> ((Nothing, oid), (val, pos))) writeSet) `M.union` values
                          else values 
                log' = if null writeSet then log else log S.|> CommitEntry writeSet readSet
            in go (TraceCommit trtId committed:acc) log' values' writeSets {- could clean up writeSets here -} readSets ops

scanTraceExecutorSpecification :: [TraceOp Int] -> [(TraceOp Int, S.Seq (TangoEntry Int), M.Map (Maybe Int, OID) (Int, Position), IM.IntMap [Position], IM.IntMap [(OID, Position)])]
scanTraceExecutorSpecification = go S.empty M.empty IM.empty IM.empty
    where go !_ !_ !_ !_ [] = []

          go log values writeSets readSets (TraceRead { traceRuntimeId = Nothing, traceOID = oid }:ops) = 
            (TraceRead Nothing oid (fst $ M.findWithDefault (0, undefined) (Nothing, oid) values), log, values, writeSets, readSets):go log values writeSets readSets ops

          go log values writeSets readSets (TraceRead { traceRuntimeId = Just rtId, traceOID = oid }:ops) = 
            let combineIfNew [(oid, pos)] old = if any (\(oid', _) -> oid' == oid) old then old else (oid,pos):old
                (value, version) = maybe (M.findWithDefault (0, -1) (Nothing, oid) values) id (M.lookup (Just rtId, oid) values)
                readSets' = IM.insertWith combineIfNew rtId [(oid, version)] readSets
            in (TraceRead (Just rtId) oid value, log, values, writeSets, readSets'):go log values writeSets readSets' ops

          go log values writeSets readSets (op@(TraceWrite { traceRuntimeId = Nothing, traceOID = oid, valueToWrite = val }):ops) =
            let log' = log S.|> UpdateEntry False True oid val
                values' = M.insert (Nothing, oid) (val, S.length log) values
            in (op, log', values', writeSets, readSets):go log' values' writeSets readSets ops

          go log values writeSets readSets (op@(TraceWrite { traceRuntimeId = Just rtId, traceOID = oid, valueToWrite = val }):ops) =
            let log' = log S.|> UpdateEntry True True oid val
                values' = M.insert (Just rtId, oid) (val, S.length log) values
                writeSets' = IM.insertWith (++) rtId [S.length log] writeSets
            in (op, log', values', writeSets', readSets):go log' values' writeSets' readSets ops

          go log values writeSets readSets (TraceCommit { traceTransactionId = trtId }:ops) = 
            let writeSet = IM.findWithDefault [] trtId writeSets
                readSet = IM.findWithDefault [] trtId readSets
                pos = S.length log
                committed = pureCheckCommitSpecification log readSet (if null writeSet then maximum (map snd readSet) else pos)
                values' = if committed then 
                            M.fromListWith (\_ x -> x) (map (\p -> case S.index log p of UpdateEntry _ _ oid val -> ((Nothing, oid), (val, pos))) writeSet) `M.union` values
                          else values 
                log' = if null writeSet then log else log S.|> CommitEntry writeSet readSet
            in (TraceCommit trtId committed, log', values', writeSets, readSets):go log' values' writeSets {- could clean up writeSets here -} readSets ops

-- Tango --------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

type OID = Int

data TangoObjectCallbacks e s = TangoObjectCallbacks {
    applyUpdate :: e -> s -> s,
    applyCheckpoint :: e -> s
  }

data TangoEntry u 
    = UpdateEntry { speculativeFlag :: !Bool, checkpointFlag :: !Bool, oid :: !OID, payload :: !u }
    | CommitEntry { writeSet :: [Position], readSet :: [(OID, Position)] } -- TODO: Incorporate key.
    | AbortEntry { writeSet :: [Position] } -- This is used to clean out speculative writes for transactions that are explicitly aborted, possibly due to a commit record not arriving in a timely manner.
  deriving ( Show, Generic )

type ListenerId = Int

data TangoRuntime' k e s = TangoRuntime {
    readLog :: Position -> IO (Maybe e),
    queryHelper :: OID -> IO (),
    updateHelper :: OID -> k -> e -> IO (),
    checkpointHelper :: OID -> e -> IO (),
    beginTransaction :: IO (TangoTransaction k e s),
    getListenerState :: OID -> ListenerId -> IO s
  }

type TangoRuntime = TangoRuntime' () Dynamic Dynamic

data TangoTransaction k e s = TangoTransaction {
    tangoTransactionRuntime :: TangoRuntime' k e s,
    commit :: IO Bool,
    abort :: IO ()
  }

data TangoRegistrar' k e s = TangoRegistrar {
    tangoRegistrarRuntime :: TangoRuntime' k e s,
    register :: OID -> (e -> s -> s) -> (e -> s) -> s -> IO ListenerId
  }

type TangoRegistrar = TangoRegistrar' () Dynamic Dynamic

checkCommit :: [(OID, Position)] -> IM.IntMap Position -> Bool
checkCommit readSet currentVersions = all (\(oid, pos) -> pos == IM.findWithDefault (-1) oid currentVersions) readSet

-- TODO: XXX There are a lot of race conditions in the below code if it were to be used in a multi-threaded context.
makeTangoRuntime :: Log (TangoEntry e) -> IO (TangoRegistrar' k e s)
makeTangoRuntime log = do
    rtVar <- newTVarIO IM.empty
    versionsVar <- newTVarIO IM.empty
    currentPosVar <- newTVarIO 0

    listenerIdRef <- newIORef 0 -- These IDs only need to be unique, not ordered, and only per OID, so this is overspecifying the behavior.

    let doUpdate rtVar versionsVar checkpointFlag oid payload pos = do
            m <- readTVarIO rtVar
            atomically $ modifyTVar' versionsVar (IM.insert oid pos)
            let !ss = IM.findWithDefault IM.empty oid m
            if checkpointFlag then do
                forM_ ss $ \(TangoObjectCallbacks { .. }, stateRef) -> do
                    modifyIORef' stateRef (const (applyCheckpoint payload))
              else do
                forM_ ss $ \(TangoObjectCallbacks { .. }, stateRef) -> do
                    modifyIORef' stateRef (applyUpdate payload)

    let syncCursor rtVar versionsVar currentPosVar cursor isSpeculative =
            let go = do
                    mentry <- cursor
                    case mentry of
                        Nothing -> return ()
                        Just (pos, entry) -> do
                            atomically $ writeTVar currentPosVar pos
                            case entry of
                                UpdateEntry { .. } | isSpeculative speculativeFlag pos -> go -- TODO: Keep track of speculative entries.
                                UpdateEntry { .. } -> do
                                    doUpdate rtVar versionsVar checkpointFlag oid payload pos
                                    go
                                CommitEntry { .. } -> do
                                    versions <- readTVarIO versionsVar
                                    when (checkCommit readSet versions) $ do
                                        forM_ writeSet $ \writePos -> do -- This is where the buffer of speculative writes would be nice to avoid hitting the log.
                                            Just (UpdateEntry { .. }) <- logRead log writePos
                                            doUpdate rtVar versionsVar checkpointFlag oid payload pos
                                    go
                                AbortEntry { .. } -> go -- TODO: If we're not tracking speculative writes, we don't need to do anything.
            in go

    return $ TangoRegistrar {
        tangoRegistrarRuntime = TangoRuntime {
            queryHelper = \_ -> do
                currentPos <- readTVarIO currentPosVar
                cursor <- logCursorFrom log currentPos
                syncCursor rtVar versionsVar currentPosVar cursor (\specFlag _ -> specFlag),

            updateHelper = \oid _key e -> logAppend log (UpdateEntry False False oid e) $> (), -- TODO: Use _key

            checkpointHelper = \oid e -> logAppend log (UpdateEntry False True oid e) $> (),

            readLog = fmap (fmap payload) . logRead log,

            getListenerState = \oid listenerId -> do
                m <- readTVarIO rtVar 
                case (m IM.! oid) IM.! listenerId of -- TODO: Handle errors nicer, but it is a user error to pass in invalid oid-listenerId pairs.
                    (_, stateRef) -> readIORef stateRef,

            beginTransaction = do
                writeSetVar <- newTVarIO []
                readSetVar <- newTVarIO []
                transactionValidRef <- newIORef True
                transRuntimeVar <- newTVarIO IM.empty
                transVersionsVar <- newTVarIO IM.empty
                transCurrentPosVar <- newTVarIO 0

                let clone oid = do
                        transRuntime <- readTVarIO transRuntimeVar
                        if oid `IM.member` transRuntime then do
                            return Nothing
                          else do
                            -- This is copying the data from the main runtime.
                            cursor <- logCursorFrom log =<< readTVarIO currentPosVar
                            syncCursor rtVar versionsVar currentPosVar cursor (\specFlag _ -> specFlag) -- Syncing isn't necessary, but it reduces the conflict window.
                            (cbs, version) <- atomically $ liftA2 (,) (IM.findWithDefault IM.empty oid <$> readTVar rtVar)
                                                                      (IM.findWithDefault (-1) oid <$> readTVar versionsVar)
                            cbs' <- forM cbs $ \(cb, stateRef) -> do
                                stateRef' <- newIORef =<< readIORef stateRef
                                return (cb, stateRef')
                            atomically $ do
                                writeTVar transRuntimeVar (IM.insert oid cbs' transRuntime)
                                modifyTVar' transVersionsVar (IM.insert oid version)
                            return (Just version)

                let checkValid = do
                        isValid <- readIORef transactionValidRef
                        when (not isValid) (ioError (userError "Transaction has been aborted."))

                let abortOp = do
                        checkValid
                        writeSet <- readTVarIO writeSetVar
                        logAppend log (AbortEntry writeSet)
                        writeIORef transactionValidRef False

                let tangoRuntime = TangoRuntime {
                        queryHelper = \oid -> do
                            checkValid
                            mversion <- clone oid
                            case mversion of
                                Nothing -> return ()
                                Just version -> atomically $ modifyTVar' readSetVar ((oid, version):)
                            currentPos <- readTVarIO transCurrentPosVar
                            cursor <- logCursorFrom log currentPos
                            writeSet <- readTVarIO writeSetVar
                            syncCursor transRuntimeVar transVersionsVar transCurrentPosVar cursor (\specFlag pos -> specFlag && pos `notElem` writeSet),
                    
                        updateHelper = \oid _key e -> do -- TODO: Use _key
                            checkValid
                            clone oid
                            pos <- logAppend log (UpdateEntry True False oid e)
                            atomically $ modifyTVar' writeSetVar (pos:),

                        checkpointHelper = \oid e -> do
                            checkValid
                            clone oid
                            pos <- logAppend log (UpdateEntry True True oid e)
                            atomically $ modifyTVar' writeSetVar (pos:),

                        readLog = (checkValid >>) . fmap (fmap payload) . logRead log,

                        getListenerState = \oid listenerId -> do
                            m <- readTVarIO transRuntimeVar 
                            case (m IM.! oid) IM.! listenerId of -- TODO: Handle errors nicer, but it is a user error to pass in invalid oid-listenerId pairs.
                                (_, stateRef) -> readIORef stateRef,

                        beginTransaction = do -- These "nested" transactions will not be isolated from other "nested" transactions.
                            checkValid
                            return $ TangoTransaction {
                                tangoTransactionRuntime = tangoRuntime,
                                commit = return True,
                                abort = abortOp
                            }
                      }

                return $ TangoTransaction {
                    tangoTransactionRuntime = tangoRuntime,
                    commit = do
                        checkValid -- <-- TODO: Race condition here, if two threads try to commit the same transaction at the same time.  Make checkValid an STM action.
                        writeIORef transactionValidRef False -- No more operations allowed for a committed transaction.
                        readSet <- readTVarIO readSetVar -- unsorted by position
                        if null readSet then do
                            writeSet <- reverse <$> readTVarIO writeSetVar -- sorted by position
                            logAppend log (CommitEntry writeSet readSet)
                            return True -- Write-only transactions always succeed. -- TODO: XXX This won't be true when others start aborting others' transactions. (See the TODO in the General case branch.)
                          else do
                            writeSet <- reverse <$> readTVarIO writeSetVar -- sorted by position
                            currentPos <- readTVarIO transCurrentPosVar
                            if null writeSet then do -- Read-only transaction, just roll forward and make sure nothing is newer than the readSet when we get current.
                                cursor <- logCursorFromTo log currentPos (maximum (map snd readSet)) -- Only need to roll-forward to the latest read, not to current. This minimizes the conflict window.
                                syncCursor transRuntimeVar transVersionsVar transCurrentPosVar cursor (\specFlag _ -> specFlag)
                                versions <- readTVarIO transVersionsVar
                                return $ checkCommit readSet versions
                              else do -- General case
                                pos <- logAppend log (CommitEntry writeSet readSet)
                                cursor <- logCursorFromTo log currentPos pos
                                -- Roll forward OVER the commit record so that it gets applied.  If it is applied, then every OID in our writeSet will have version equal to pos.
                                syncCursor transRuntimeVar transVersionsVar transCurrentPosVar cursor (\specFlag _ -> specFlag)
                                -- TODO: If this sync sees a commit record whose writeSet intersects with ours (which should only ever be an
                                -- abort record), we need to abort this transaction as well.
                                versions <- readTVarIO transVersionsVar
                                -- Just need to find one OID in the writeSet and verify that it's version == pos.
                                -- TODO: Can I do this cleanly without hitting the log?  I mean I could just store the OID of the first object upon which updateHelper
                                -- is called and use that, but that's kind of janky.
                                Just (UpdateEntry { oid = oid }) <- logRead log (head writeSet)
                                return $ versions IM.! oid == pos,
                                
                    abort = abortOp
                }
        },
        register = \oid appUpdate appCheckpoint initState -> do
            listenerId <- atomicModifyIORef' listenerIdRef (\n -> (n+1, n+1))
            stateRef <- newIORef initState
            atomically $ modifyTVar' rtVar (IM.insertWith IM.union oid (IM.singleton listenerId (TangoObjectCallbacks appUpdate appCheckpoint, stateRef)))
            return listenerId
    }

-- Tango Objects ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

data TangoRegister a = TangoRegister {
    readRegister :: TangoRuntime -> IO a,
    writeRegister :: TangoRuntime -> a -> IO ()
 }

makeRegister :: (Typeable a) => TangoRegistrar -> OID -> a -> IO (TangoRegister a)
makeRegister (TangoRegistrar { register = register }) oid start = do
    listenerId <- register oid const id (toDyn start)
    return $ TangoRegister {
        readRegister = \rt -> do
            queryHelper rt oid
            mr <- fromDynamic <$> getListenerState rt oid listenerId
            case mr of Just r -> return r,
        writeRegister = \rt -> checkpointHelper rt oid . toDyn
    }

data TangoMap k v = TangoMap {
    get :: TangoRuntime -> k -> IO v,
    put :: TangoRuntime -> k -> v -> IO ()
  }

makeTangoMap :: forall k v. (Ord k, Typeable k, Typeable v) => TangoRegistrar -> OID -> IO (TangoMap k v)
makeTangoMap (TangoRegistrar { register = register }) oid = do
    listenerId <- register oid (\dkv dm -> case (fromDynamic dkv, fromDynamic dm) of (Just (k, v), Just m) -> toDyn (M.insert k v m :: M.Map k v)) id (toDyn (M.empty :: M.Map k v))
    return $ TangoMap {
        get = \rt k -> do
            queryHelper rt oid
            mm <- fromDynamic <$> getListenerState rt oid listenerId
            case mm of Just m -> return $ m M.! k,
        put = \rt k v -> updateHelper rt oid () (toDyn (k, v))
    }

-- Traces -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

data TraceOp a
    = TraceRead { traceRuntimeId :: !(Maybe Int), traceOID :: !OID, expectedResult :: !a }
    | TraceWrite { traceRuntimeId :: !(Maybe Int), traceOID :: !OID, valueToWrite :: !a }
    | TraceCommit { traceTransactionId :: !Int, commitSucceeded :: !Bool }
  deriving (Eq, Show)

showStep :: (Show a) => TraceOp a -> String
showStep (TraceRead {..}) = maybe ('*':) shows traceRuntimeId $ ": read r" ++ show traceOID
showStep (TraceWrite {..}) = maybe ('*':) shows traceRuntimeId $ ':':' ':'r':show traceOID ++ " := " ++ show valueToWrite
showStep (TraceCommit {..}) = shows traceTransactionId ": commit"

parseTraceOp :: (Read a, Num a) => String -> Either String (TraceOp a)
parseTraceOp s0 = 
    case eatWhitespace s0 of
        c:':':s1 -> case eatWhitespace s1 of
                        'c':'o':'m':'m':'i':'t':_ -> if isDigit c then Right (TraceCommit (digitToInt c) False) else Left "Transaction indicator can't be '*' for \"commit\"."
                        'r':'e':'a':'d':' ':s2 -> case eatWhitespace s2 of
                                                    'r':r:_ | isDigit r -> (\rt -> TraceRead rt (digitToInt r) 0)  <$> toRuntime c
                                                    _ -> Left "Expected digit for register."
                        'r':r:s2 | isDigit r -> case eatWhitespace s2 of
                                                    ':':'=':' ':s3 -> case reads (eatWhitespace s3) of
                                                                        [(v,_)] -> (\rt -> TraceWrite rt (digitToInt r) v) <$> toRuntime c
                                                                        _ -> Left "Expected number."
                                                    _ -> Left "Expected \":=\"."
                        _ -> Left "Expected \"read\", \"commit\", or assignment."
        _ -> Left "Expected transaction indicator, digit or '*'."                                                                 
  where eatWhitespace = dropWhile isSpace
        toRuntime '*' = Right Nothing
        toRuntime d | isDigit d = Right (Just (digitToInt d))
        toRuntime _ = Left "Invalid transaction indicator"

playTrace :: (Show a, Eq a, Typeable a) => TangoRegistrar -> a -> [TraceOp a] -> IO Bool  
playTrace registrar@(TangoRegistrar { tangoRegistrarRuntime = runtime }) initState = go IM.empty IM.empty True
    where ensureRuntime trts Nothing = return (trts, runtime)
          ensureRuntime trts (Just rtId) = do
            case IM.lookup rtId trts of
                Nothing -> do
                    trt <- beginTransaction runtime
                    return (IM.insert rtId trt trts, tangoTransactionRuntime trt)
                Just rt -> return (trts, tangoTransactionRuntime rt)

          ensureRegister regs oid = do
            case IM.lookup oid regs of
                Nothing -> do
                    reg <- makeRegister registrar oid initState
                    return (IM.insert oid reg regs, reg)
                Just reg -> return (regs, reg)

          go !_ !_ !passed [] = return passed
          go !trts !regs !passed (op@(TraceWrite runtimeId oid valueToWrite):rest) = do
            putStr "    " >> print op
            (trts, rt) <- ensureRuntime trts runtimeId
            (regs, reg) <- ensureRegister regs oid
            writeRegister reg rt valueToWrite
            go trts regs passed rest
          go !trts !regs !passed (op@(TraceRead runtimeId oid expected):rest) = do
            putStr "    " >> print op
            (trts, rt) <- ensureRuntime trts runtimeId
            (regs, reg) <- ensureRegister regs oid
            actual <- readRegister reg rt 
            when (actual /= expected) $ do
                setSGR [SetColor Foreground Vivid Red]
                putStrLn $ "    **** Actual value " ++ show actual ++ " does not equal expected value " ++ show expected ++ "!"
                setSGR [Reset]
            go trts regs (passed && actual == expected) rest
          go !trts !regs !passed (op@(TraceCommit transactionId expected):rest) = do
            putStr "    " >> print op
            let trt = trts IM.! transactionId
            actual <- commit trt
            when (actual /= expected) $ do
                setSGR [SetColor Foreground Vivid Red]
                putStrLn $ "    **** Actual value " ++ show actual ++ " does not equal expected value " ++ show expected ++ "!"
                setSGR [Reset]
            go trts regs (passed && actual == expected) rest

runTrace :: [TraceOp Int] -> IO Bool
runTrace executionTrace = do
    log <- makeInMemoryLog
    rt <- makeTangoRuntime log
    result <- playTrace rt (0 :: Int) executionTrace 
    setSGR [SetConsoleIntensity BoldIntensity]
    putStrLn "\nLog:"
    setSGR [Reset]
    setSGR [SetColor Foreground Dull Yellow]
    printLog log
    setSGR [Reset]
    return result

loadTraceFromFile :: FilePath -> IO [TraceOp Int]
loadTraceFromFile path = do
    result <- Csv.decode Csv.NoHeader <$> LBS.readFile path
    case result of  
        Left err -> print err >> return []
        Right executionTrace -> return $ toList executionTrace

runTraceFromFile :: FilePath -> IO Bool
runTraceFromFile path = do
    result <- Csv.decode Csv.NoHeader <$> LBS.readFile path
    case result of  
        Left err -> print err >> return False
        Right executionTrace -> runTrace (toList executionTrace)

runTracesFromDirectory :: FilePath -> IO Bool
runTracesFromDirectory directory = do
    files <- filter (".csv" `isSuffixOf`) <$> getDirectoryContents directory
    results <- forM files $ \file -> do
        setSGR [SetConsoleIntensity BoldIntensity, SetColor Foreground Vivid White]
        putStrLn $ file++":"
        setSGR [Reset]
        result <- runTraceFromFile (directory ++ file)
        if result then do
            setSGR [SetConsoleIntensity BoldIntensity, SetColor Foreground Vivid Green]
            putStrLn "*** Passed"
            setSGR [Reset]
          else do
            setSGR [SetConsoleIntensity BoldIntensity, SetColor Foreground Vivid Red]
            putStrLn "*** Failed"
            setSGR [Reset]
        putStrLn ""
        return result
    return (and results)

-- op | rt | oid | value
instance (Csv.FromField a) => Csv.FromRecord (TraceOp a) where
    parseRecord v = do
        op <- v .! 0
        case op of 
            "Read" -> TraceRead <$> parseRuntime (v .! 1) <*> v .! 2 <*> v .! 3
            "Write" -> TraceWrite <$> parseRuntime (v .! 1) <*> v .! 2 <*> v .! 3
            "Commit" -> TraceCommit <$> v .! 1 <*> fmap read (v .! 3)
            _ -> empty
      where parseRuntime = fmap (\s -> if null s then Nothing else Just (read s))


-- Example ------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------

setup1 = do
    log <- makeInMemoryLog
    rt <- makeTangoRuntime log

    r1 <- makeRegister rt 1 (0 :: Int)
    r2 <- makeRegister rt 2 (0 :: Int)

    return (log, tangoRegistrarRuntime rt, r1, r2)

example1 = do
    (log, rt, r1, r2) <- setup1

    x1 <- readRegister r1 rt 
    x2 <- readRegister r2 rt 
    writeRegister r1 rt (x1+10)
    writeRegister r2 rt (x2+100)

    printLog log

    print' "r1" =<< readRegister r1 rt 
    print' "r2" =<< readRegister r2 rt 

example2 = [
    TraceRead {traceRuntimeId = Just 1, traceOID = 2, expectedResult = 0 :: Int},
    TraceRead {traceRuntimeId = Just 2, traceOID = 1, expectedResult = 0},
    TraceRead {traceRuntimeId = Just 2, traceOID = 2, expectedResult = 0},
    TraceWrite {traceRuntimeId = Just 1, traceOID = 1, valueToWrite = -100},
    TraceWrite {traceRuntimeId = Just 1, traceOID = 2, valueToWrite = 100},
    TraceWrite {traceRuntimeId = Just 2, traceOID = 1, valueToWrite = -333},
    TraceWrite {traceRuntimeId = Just 2, traceOID = 2, valueToWrite = 333},
    TraceCommit {traceTransactionId = 1, commitSucceeded = True},
    TraceCommit {traceTransactionId = 2, commitSucceeded = False},
    TraceRead {traceRuntimeId = Nothing, traceOID = 1, expectedResult = -100},
    TraceRead {traceRuntimeId = Nothing, traceOID = 2, expectedResult = 100}
  ]

runTraces = runTracesFromDirectory "./traces/"

testSpecification = do    
    let directory = "./traces/"
    files <- filter (".csv" `isSuffixOf`) <$> getDirectoryContents directory
    results <- forM files $ \file -> do
        setSGR [SetConsoleIntensity BoldIntensity, SetColor Foreground Vivid White]
        putStrLn $ file++":"
        setSGR [Reset]
        traceOps <- loadTraceFromFile (directory ++ file)
        let traceOps' = traceExecutorSpecification traceOps
        let result = traceOps == traceOps'
        setSGR [SetColor Foreground Dull Yellow]
        mapM_ print traceOps
        setSGR [Reset]
        putStrLn ""
        setSGR [SetColor Foreground Vivid Yellow]
        mapM_ print traceOps'
        setSGR [Reset]
        if result then do
            setSGR [SetConsoleIntensity BoldIntensity, SetColor Foreground Vivid Green]
            putStrLn "*** Passed"
            setSGR [Reset]
          else do
            setSGR [SetConsoleIntensity BoldIntensity, SetColor Foreground Vivid Red]
            putStrLn "*** Failed"
            setSGR [Reset]
        putStrLn ""
        return result
    return (and results)
