module Main where

import Chain (TensorData(..), chainM, chainM2, chainT)
import qualified Data.HashMap.Strict as Map
import qualified Data.Vector as V

main :: IO ()
main = do
    let tensors = map (Map.fromList) [
                [(1,4),(2,3)],
                [(2,3),(3,5)],
                [(3,5),(4,2)],
                [(4,2),(5,4)],
                [(5,4),(6,3)],
                [(6,3),(7,2)]
            ]

        matrices = [4,3,5,2,4,3,2]

    putStrLn . show $ chainM matrices
    putStrLn . show $ chainM2 matrices
    putStrLn . show . totalCost . chainT $ V.fromList tensors
    putStrLn . show . recipe . chainT $ V.fromList tensors
