{-# LANGUAGE ForeignFunctionInterface #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE JavaScriptFFI #-}
{-# LANGUAGE OverloadedStrings #-}
module Main where

import qualified Data.Aeson as AE -- aeson
import Data.Aeson ( (.=) ) -- aeson
import Data.Foldable ( toList, foldl' ) -- base
import Data.IORef ( newIORef, atomicModifyIORef', writeIORef ) -- base
import qualified Data.IntMap as IM -- containers 
import qualified Data.Map as M -- containers
import Data.Maybe ( catMaybes ) -- base
import qualified Data.Sequence as S -- containers?
import Data.String ( IsString(..) ) -- base
import qualified Data.Text as T -- text
import qualified Data.Vector as V -- vector
import GHCJS.Foreign.Callback ( Callback, syncCallback, syncCallback1, OnBlocked(..) ) -- ghcjs-base?
import GHCJS.Marshal ( toJSVal ) -- ghcjs-base
import GHCJS.Marshal.Pure ( pFromJSVal ) -- ghcjs-base
import GHCJS.Types ( JSVal ) -- ghcjs-base
import JavaScript.Array ( JSArray, fromList ) -- ghcjs-base

import TangoFP

curryMap :: (Ord a, Ord b) => M.Map (a, b) c -> M.Map a (M.Map b c)
curryMap = foldl' (\m ((a,b),c) -> M.insertWith M.union a (M.singleton b c) m) M.empty . M.assocs

{-
renderLog([
    {registers: [{name: 'r1', value: 100}], entry: { type: 'update', speculative: false, checkpoint: true, oid: 1, value: 100 } }
]);

renderTransactions({
    '1': [
        {position: 0, registers: [{name: 'r1', value: 100}], readSet: [], status: 'undecided'}, 
        {position: 3, registers: [{name: 'r1', value: 100},{name: 'r2', value: 123}], readSet: [1,2], status: 'committed'}]
});
-}

traceOps :: [TraceOp Int]
traceOps = [
    TraceWrite {traceRuntimeId = Nothing, traceOID = 1, valueToWrite = 0 :: Int},
    TraceWrite {traceRuntimeId = Nothing, traceOID = 2, valueToWrite = 0},
    TraceRead {traceRuntimeId = Just 1, traceOID = 1, expectedResult = 0},
    TraceRead {traceRuntimeId = Just 1, traceOID = 2, expectedResult = 0},
    TraceRead {traceRuntimeId = Just 2, traceOID = 1, expectedResult = 0},
    TraceRead {traceRuntimeId = Just 2, traceOID = 2, expectedResult = 0},
    TraceWrite {traceRuntimeId = Just 1, traceOID = 1, valueToWrite = -100},
    TraceWrite {traceRuntimeId = Just 1, traceOID = 2, valueToWrite = 100},
    TraceWrite {traceRuntimeId = Just 2, traceOID = 1, valueToWrite = -333},
    TraceWrite {traceRuntimeId = Just 2, traceOID = 2, valueToWrite = 333},
    TraceCommit {traceTransactionId = 1, commitSucceeded = True},
    TraceCommit {traceTransactionId = 2, commitSucceeded = False}
  ]

steps = map showStep traceOps

translate :: (TraceOp Int, S.Seq (TangoEntry Int), M.Map (Maybe Int, OID) (Int, Position), IM.IntMap [Position], IM.IntMap [(OID, Position)]) -> AE.Value
translate (op, log, values, writeSets, readSets) = AE.object ["log" .= log', "transactions" .= AE.object transactions]
    where log' = AE.Array (V.fromList $ map (\entry -> AE.object ["registers".= translateRegisters mainRegisters, "entry" .= translateEntry entry]) $ toList log)

          mainRegisters = maybe M.empty id $ M.lookup Nothing cvalues

          translateRegisters = map (\(k,v) -> AE.object ["name" .= ('r':show k), "value" .= v]) . M.assocs

          transactions = map (\txId -> fromString (show txId) .= buildTransaction txId) transactionIds
            where transactionIds = case op of  --catMaybes (M.keys cvalues)
                                    TraceRead { traceRuntimeId = Just txId } -> [txId]
                                    TraceWrite { traceRuntimeId = Just txId } -> [txId]
                                    TraceCommit { traceTransactionId = txId } -> [txId]
                                    _ -> [] 

          buildTransaction txId = 
            case op of 
                TraceRead {} -> AE.object ["readSet" .= rs]
                TraceCommit {..} -> AE.object [   
                    "readSet" .= rs,
                    "write" .= AE.object [
                        "position" .= (if null (IM.findWithDefault [] txId writeSets) then maximum rs else S.length log - 1),
                        "registers" .= translateRegisters (vs `M.union` M.filterWithKey (\k _ -> k `elem` rs) mainRegisters),
                        "status" .= (if commitSucceeded then "committed" else "aborted" :: T.Text)]]
                TraceWrite {} -> AE.object [   
                    "readSet" .= rs,
                    "write" .= AE.object [
                        "position" .= (S.length log - 1),
                        "registers" .= translateRegisters (vs `M.union` M.filterWithKey (\k _ -> k `elem` rs) mainRegisters),
                        "status" .= ("undecided" :: T.Text)]]
           where rs = reverse $ map snd (IM.findWithDefault [] txId readSets)
                 vs = maybe M.empty id $ M.lookup (Just txId) cvalues

          translateEntry (UpdateEntry {..}) = 
            AE.object [
                "type" .= ("update" :: T.Text),
                "oid" .= oid, 
                "speculative" .= speculativeFlag,
                "checkpoint" .= checkpointFlag,
                "value" .= payload]
          translateEntry (CommitEntry {..}) =
            AE.object [
                "type" .= ("commit" :: T.Text),
                "writeSet" .= writeSet,
                "readSet" .= map snd readSet]

          cvalues = curryMap $ M.map fst values

main = do
    xs <- mapM (\state -> toJSVal $ AE.object ["steps" .= steps, "state" .= translate state]) $ scanTraceExecutorSpecification traceOps
    stepsRef <- newIORef xs
    let onAdvance = do
          xs <- atomicModifyIORef' stepsRef (\xs -> (case xs of [] -> []; _:xs' -> xs', xs))
          sendData $ fromList xs
    
    let parseSteps s = do
          let steps = lines (pFromJSVal s)
          case mapM parseTraceOp steps of
            Right traceOps -> do
                xs <- mapM (\state -> toJSVal $ AE.object ["steps" .= steps, "state" .= translate state]) $ scanTraceExecutorSpecification traceOps
                writeIORef stepsRef xs
                onAdvance
            Left err -> putStrLn err

    advanceCallback <- syncCallback ContinueAsync onAdvance
    setAdvanceCallback advanceCallback

    parseStepsCallback <- syncCallback1 ContinueAsync parseSteps
    setParseStepsCallback parseStepsCallback

foreign import javascript unsafe "onData($1);" sendData :: JSArray -> IO ()

foreign import javascript unsafe "haskell.advance = $1;" setAdvanceCallback :: Callback a -> IO ()

foreign import javascript unsafe "haskell.parseSteps = $1;" setParseStepsCallback :: Callback a -> IO ()
