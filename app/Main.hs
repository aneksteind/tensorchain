{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Main where

import Data.List (tails, product)
import Data.List.Extras (argmin)
import qualified Data.HashMap.Strict as Map
import Data.HashMap.Strict ((!), difference)
import Data.Maybe (fromMaybe)
import Debug.Trace (trace)

import           Data.Vector (Vector)
import qualified Data.Vector as V

type Map = Map.HashMap

data TensorLink = TL { left :: Maybe Int, right :: Maybe Int, free :: [Int]}
type Path = [TensorLink]

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

-- dynamorphism
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
            as = [(dims !! (i-1)) * (dims !! k) * (dims !! j) + (table `get` offset k)| k <- [i..j-1]]
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

chain :: Path -> Int
chain tensors = dyna triangle findParen range where

    dimsFromSize (t:[]) = [left t, right t]
    dimsFromSize (t:xs) = left t : dimsFromSize xs

    dims = dimsFromSize tensors

    range@(start,end) = (1, length dims - 1)

    -- stores the product of all free indices from tensor i through j, inclusive
    p i j = product . concatMap free . take (j-i) $ drop i tensors
    bundle = Map.fromList [((i,j),(p i j)) | j <- [1..end], i <- [0..j-1] ]

    -- gets the product of all bound indices
    ctime = product . map ((fromMaybe 1) . (dims !!))

    triangle :: (Int,Int) -> ListF (Int,Int) (Int,Int)
    triangle (1,1) = Some (1,1)
    triangle (i,j)
        | i == j = Cons (i,j) (1,j-1)
        | otherwise = Cons (i,j) (i+1,j)

    findParen :: ListF (Int,Int) (Cofree (ListF (Int,Int)) Int) -> Int
    findParen (Some _) = 0
    findParen (Cons (i,j) table)
        | i == j = 0
        | i < j = minimum (zipWith (+) as bs) where
            as = [ctime [i-1, j, k] * bundle ! (i-1,j) + table `get` offset k| k <- [i..j-1]]
            bs = table `collect` (j-i)
            offset k = ((j*(j+1) - k*(k+1)) `div` 2) - 1

chain2 :: Path -> Int
chain2 tensors = final where

    final = (hylo triangle findParen range) ! range

    range@(start,end) = (1, length dims - 1)

    dims = dimsFromSize tensors

    dimsFromSize (t:[]) = [left t, right t]
    dimsFromSize (t:xs) = left t : dimsFromSize xs

    -- stores the product of all free indices from tensor i through j, inclusive
    p i j = product . concatMap free . take (j-i) $ drop i tensors

    -- gets the product of all bound indices
    ctime = product . map ((fromMaybe 1) . (dims !!))

    triangle :: (Int,Int) -> ListF (Int,Int) (Int,Int)
    triangle (1,1) = Some (1,1)
    triangle (i,j)
        | i == j = Cons (i,j) (1,j-1)
        | otherwise = Cons (i,j) (i+1,j)

    findParen :: ListF (Int,Int) (Map (Int,Int) Int) -> (Map (Int,Int) Int)
    findParen (Some _) = Map.fromList [((i,i),0) | i <- [1..end]]
    findParen (Cons (i,j) table)
        | i == j = table
        | i < j = Map.insert (i,j) (minimum parenthesizations) table where
            cost x y = table ! (x,y)
            bundleSize = p (i-1) j
            parenthesizations = [ctime [i-1, j, k] * bundleSize + cost i k + cost (k+1) j | k <- [i..j-1]]

-- find the best ordering for a collection of tensors: O((N+R)N^3)
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
    findParen (Cons (i,j) table) -- O(N^2) per (i,j)
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

tspace = Map.foldl (*) 1

-- find the best ordering for a collection of tensors: O((N+R)N^3)
chain4:: [Tensor] -> TensorData
chain4 tensors = best where

    best = (hylo triangle findParen range) ! range
    range@(start,end) = (1, length tensors)

    emptyData i = TensorData {
        totalCost = 0,
        recipe = Tensor i,
        cspace = tspace $ tensors !! (i-1),
        indices = tensors !! (i-1)
    }

    triangle :: (Int,Int) -> ListF (Int,Int) (Int,Int)
    triangle (1,1) = Some (1,1)
    triangle (i,j)
        | i == j = Cons (i,j) (1,j-1)
        | otherwise = Cons (i,j) (i+1,j)

    findParen :: Algebra (ListF (Int,Int)) (Map (Int,Int) TensorData)
    findParen (Some (t,_)) = Map.insert (t,t) (emptyData t) Map.empty -- O(N)
    findParen (Cons (i,j) table) -- O(N^2)
        | i == j = Map.insert (i,j) (emptyData i) table -- O(N)
        | i < j = Map.insert (i,j) min table where
            
            splits = [((i,k),(k+1,j)) | k <- [i..j-1]] -- O(N)
            contractionDataPairs = map (\(left,right) -> (table ! left, table ! right)) splits -- O(N)
            parenthesizations = map contract contractionDataPairs -- O(N)
            min = argmin totalCost parenthesizations -- O(N)

            -- get contraction data of combining two intermediate tensors: O(1)
            contract :: (TensorData, TensorData) -> TensorData
            contract (left,right) = TensorData {
                totalCost = totalCost left + totalCost right + cspaceij,
                recipe = Intermediate (recipe left) (recipe right),
                cspace = cspaceij,
                indices = symdiff
            } where
                (indLeft, indRight) = (indices left, indices right)
                cspaceij = tspace $ (indLeft <> indRight)
                symdiff = (indLeft \\ indRight) <> (indRight \\ indLeft)

chain5 :: Path -> Int
chain5 tensors = V.head $ hylo triangle findParen range where

    dimsFromSize (t:[]) = [left t, right t]
    dimsFromSize (t:xs) = left t : dimsFromSize xs

    dims = dimsFromSize tensors

    range@(start,end) = (1, length dims - 1)

    -- stores the product of all free indices from tensor i through j, inclusive
    p i j = product . concatMap free . take (j-i) $ drop i tensors
    bundle = Map.fromList [((i,j),(p i j)) | j <- [1..end], i <- [0..j-1] ]

    -- gets the product of all bound indices
    ctime = product . map ((fromMaybe 1) . (dims !!))

    triangle :: (Int,Int) -> ListF (Int,Int) (Int,Int)
    triangle (1,1) = Some (1,1)
    triangle (i,j)
        | i == j = Cons (i,j) (1,j-1)
        | otherwise = Cons (i,j) (i+1,j)

    findParen :: Algebra (ListF (Int,Int)) (V.Vector Int)
    findParen (Some _) = V.cons 0 V.empty
    findParen (Cons (i,j) table)
        | i == j = V.cons 0 table
        | i < j = V.cons min table where
            min = minimum (zipWith (+) as bs)
            as = [ctime [i-1, j, k] * bundle ! (i-1,j) + ((V.!) table $ offset k)| k <- [i..j-1]]
            bs = V.toList $ V.take (j-i) table 
            offset k = ((j*(j+1) - k*(k+1)) `div` 2) - 1

main :: IO ()
main = do
    let tensors = [
                    TL Nothing (Just 20) [40],
                    TL (Just 20) (Just 30) [],
                    TL (Just 30) (Just 10) [],
                    TL (Just 10) Nothing [30]
                    -- TL (Just 4) Nothing [3]
                    ]
        result1 = chain tensors
        result2 = chain2 tensors

        tensors2 = map (Map.fromList) [
                [(1,40),(2,20)],
                [(2,20),(3,30)],
                [(3,30),(4,10)],
                [(4,10),(5,30)]
            ]
            
        result3 = chainT $ V.fromList tensors2
        result4 = chain4 tensors2
        result5 = chain5 tensors

    let matrices = [4,3,5,2,4,3,2]
    putStrLn . show $ chainM matrices
    putStrLn . show $ chainM2 matrices
    
    putStrLn $ show (result1, result2, totalCost result3, totalCost result4, result5)
    putStrLn . show $ recipe result3


-- [(2,3,[1,2]), (3,5,[2,2]), (5,2,[1,3]), (2,4,[3,2]), (4,3,[4,2])]
-- [(2,[1,2]), (3, [2,2]), (5, [1,3]), (2, [3,2]), (4, [4,2]), (3, [])]
