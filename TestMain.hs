module Main where
import Control.Monad ( when ) -- base
import System.Exit ( exitFailure ) -- base
import TangoFP ( runTraces, testSpecification )

main = do 
    result <- runTraces
    when (not result) exitFailure

    result <- testSpecification
    when (not result) exitFailure
