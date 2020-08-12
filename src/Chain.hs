module Chain
    ( chainM
    , chainM2
    , chainT
    , TensorData(..)
    ) where

import Data.List.Extras (argmin)
import qualified Data.HashMap.Strict as Map
import Data.HashMap.Strict ((!), difference)

import           Data.Vector (Vector)
import qualified Data.Vector as V

type Map = Map.HashMap

data ListF v x = Some v | Cons v x deriving Show
instance Functor (ListF v) where
    fmap f (Some v) = Some v
    fmap f (Cons v x) = Cons v (f x)

type Algebra f a = f a -> a
type CoAlgebra f a = a -> f a

type Tensor = Map Int Int

data ContractionTree a = 
    Tensor a 
  | Intermediate (ContractionTree a) (ContractionTree a)

instance Show a => Show (ContractionTree a) where
    show (Tensor a) = show a
    show (Intermediate l r) = "(" ++ show l ++ " " ++ show r ++ ")"

data TensorData = TensorData {
    totalCost :: Int,
    recipe :: ContractionTree Int,
    cspace :: Int,
    indices :: Tensor
}

(\\) = difference

data Cofree f a = a :< (f (Cofree f a))

extract :: Cofree f a -> a
extract (a :< _) = a

get :: Cofree (ListF v) a -> Int -> a
get (x :< xs) 0 = x
get (x :< (Cons _ xs)) n = xs `get` (n-1)

collect :: Cofree (ListF v) a -> Int -> [a]
collect _ 0 = []
collect (x :< (Some _)) n = [x]
collect (x :< (Cons _ cf)) n = x : cf `collect` (n-1)

hylo :: Functor f => CoAlgebra f a -> Algebra f b -> a -> b
hylo f g = h where h = g . fmap h . f

dyna :: (Functor f, Show b, Show (f b)) => (a -> f a) -> (f (Cofree f b) -> b) -> a -> b
dyna f g = extract . hylo f (\fcfb -> (g fcfb) :< fcfb)

chainM :: [Int] -> Int
chainM dims = dyna triangle findParen range where

    range = (1, length dims - 1)

    triangle :: (Int,Int) -> ListF (Int,Int) (Int,Int)
    triangle (1,1) = Some (1,1)
    triangle (i,j)
        | i == j = Cons (i,j) (1,j-1)
        | otherwise = Cons (i,j) (i+1,j)

    findParen :: ListF (Int,Int) (Cofree (ListF (Int,Int)) Int) -> Int
    findParen (Some j) = 0
    findParen (Cons (i,j) table)
        | i == j = 0
        | i < j = minimum (zipWith (+) as bs) where
            as = [(dims !! (i-1)) * (dims !! k) * (dims !! j) 
                   + (table `get` offset k) | k <- [i..j-1]]
            bs = table `collect` (j-i)
            offset k = ((j*(j+1) - k*(k+1)) `div` 2) - 1

chainM2 :: [Int] -> Int
chainM2 dims = best where
    best = (hylo triangle findParen range) ! range

    range = (1, length dims - 1)

    triangle :: (Int,Int) -> ListF (Int,Int) (Int,Int)
    triangle (1,1) = Some (1,1)
    triangle (i,j)
        | i == j = Cons (i,j) (1,j-1)
        | otherwise = Cons (i,j) (i+1,j)

    findParen :: Algebra (ListF (Int,Int)) (Map (Int,Int) Int)
    findParen (Some (j,_)) = Map.insert (j,j) 0 Map.empty
    findParen (Cons (i,j) table)
        | i == j = Map.insert (i,j) 0 table
        | i < j = Map.insert (i,j) (minimum parenthesizations) table where
            cost x y = table ! (x,y)
            space (x,y,z) = (dims !! x) * (dims !! y) * (dims !! z)
            parenthesizations = 
                [space (i-1,k,j) + cost i k + cost (k+1) j | k <- [i..j-1]]

tspace = Map.foldl (*) 1

-- find the best ordering for a collection of tensors: O(N^3+RN^2)
chainT :: Vector Tensor -> TensorData
chainT tensors = best where

    best = (hylo triangle findParen range) ! range
    range = (1, length tensors)

    emptyData i = TensorData {
        totalCost = 0,
        recipe = Tensor i,
        cspace = tspace t,
        indices = t
    } where t = (V.!) tensors (i-1)

    triangle :: (Int,Int) -> ListF (Int,Int) (Int,Int)
    triangle (1,1) = Some (1,1)
    triangle (i,j)
        | i == j = Cons (i,j) (1,j-1)
        | otherwise = Cons (i,j) (i+1,j)

    findParen :: Algebra (ListF (Int,Int)) (Map (Int,Int) TensorData)
    findParen (Some (t,_)) = Map.insert (t,t) (emptyData t) Map.empty -- O(R)
    findParen (Cons (i,j) table) -- O(R + N) per (i,j)
        | i == j = Map.insert (i,j) (emptyData i) table -- O(R)
        | i < j = Map.insert (i,j) best table where

            -- O(R)
            indLeft = indices $ table ! (i,i)
            indNext = indices $ table ! (i+1,j)
            symdiff = (indLeft \\ indNext) <> (indNext \\ indLeft)
            cspaceij = tspace symdiff
            
            -- O(N)
            splits = [((i,k),(k+1,j)) | k <- [i..j-1]]
            getData (l,r) = (table ! l, table ! r)
            parenthesizations = map (contract . getData) splits
            best = argmin totalCost parenthesizations

            -- O(1)
            -- get contraction data of combining two intermediate tensors
            contract :: (TensorData, TensorData) -> TensorData
            contract (left,right) = TensorData {
                totalCost = totalCost left + totalCost right + sqrtCspaces,
                recipe = Intermediate (recipe left) (recipe right),
                cspace = cspaceij,
                indices = symdiff
            } where
                cspaces = cspace left * cspace right * cspaceij
                sqrtCspaces = round . sqrt . fromIntegral $ cspaces
