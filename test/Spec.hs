
import  Data.Map (Map)
import qualified Data.Map as M
import qualified Data.HashMap.Strict as H
import qualified Data.Vector as V
import Chain (chainT, chainTBF, TensorData(..))
import Test.QuickCheck
import Debug.Trace


-- check that solving using the dynamic programming
-- approach matches the brute force approach
prop_matchBF :: NonEmptyList Word -> Word -> Bool
prop_matchBF (NonEmpty edges) order = dp == bf where
    dp = totalCost $ chainT tc
    bf = chainTBF tc

    size = length edges
    
    edgeInfo :: [(Int,Integer)]
    edgeInfo = map (\(e,w) -> (e, fromIntegral w)) $ zip [1..size] edges

    tc = V.fromList [H.fromList edgeInfo | _ <- [1..order+3]]



main :: IO ()
main = quickCheckWith stdArgs {maxSuccess = 1000, maxSize = 13} prop_matchBF
