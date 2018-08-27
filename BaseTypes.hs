module BaseTypes where

import Data.List
import qualified Data.Map as Map
import qualified Data.Set as Set
import Debug.Trace

type Actor = String
type VariableName = String
type ConstantValue = String
type SetName = String
type PredicateName = String
type PropertyName = String

data TraceType = Agents | Planning | AbstractExecution 

data MOptions = MainOptions { suspicions :: Int, alpha :: Float, iterations :: Int, commitment :: Float }


notrace _ a = a

mytrace :: TraceType -> String -> a -> a
mytrace Agents = notrace
mytrace Planning = notrace
mytrace AbstractExecution = notrace


type VarMap = Map.Map VariableName ConstantValue

data Op = AtLeast | AtMost
        deriving (Show, Read, Eq, Ord)

cmpprob :: Op -> Float -> Float -> Bool
cmpprob AtLeast a b = a <= b
cmpprob AtMost a b = a >= b

data AtProp a = Predicate a [a]
            deriving (Show, Read, Eq, Ord)

            
            
{-symdiff :: Eq a => [a] -> [a] -> [a]-}
symdiff :: Ord a => Set.Set a -> Set.Set a -> Set.Set a
symdiff a b = if Set.null b then a else if Set.null a then b else ((a Set.\\ b) `Set.union`  (b Set.\\ a))

cleanup :: [Maybe a] -> [a]
cleanup [] = []
cleanup (Just x:xs) = x:(cleanup xs)
cleanup (Nothing:xs) = cleanup xs

data Context = GameContext {
              sets :: Map.Map String [String],
              setsi :: Map.Map Int [Int],
              signatures :: Map.Map String [String], -- for predicates, which types the arguments should range over ... e.g. at(c, p, i) -> [Cards, Players, Indices]
              signaturesi :: Map.Map Int [Int],
              ids :: Map.Map String Int,
              rids :: Map.Map Int String,
              actors :: [String], -- All actors
              static_predicates :: Map.Map String [[String]], -- predicates that are never changed by actions
              restricted_predicates :: Map.Map String [[String]], -- predicates that are known to only hold on a subset (e.g. because of a functional dependency between arguments)              
              indexed :: [String],
              indexedi :: [Int]
          }
          deriving (Show, Eq)
          
convertID ids x = Map.findWithDefault (-1) x ids
convertRID rids x = Map.findWithDefault "unknown" x rids

intToStr ctx x = convertRID (rids ctx) x
strToInt ctx x = convertID (ids ctx) x

accum l m = l ++ [(length m)]

toInt :: String -> Int
toInt ('0':[]) = 0
toInt ('1':[]) = 1
toInt ('2':[]) = 2
toInt ('3':[]) = 3
toInt ('4':[]) = 4
toInt ('5':[]) = 5
toInt ('6':[]) = 6
toInt ('7':[]) = 7
toInt ('8':[]) = 8
toInt ('9':[]) = 9
toInt x = (read x) :: Int

one :: Float
one = fromIntegral 1
zero :: Float
zero = fromIntegral 0

drop1 (a,b,c) = (b,c)
snd3 (a,b,c) = b
          
convertMap :: Map.Map String [String] -> Map.Map String Int -> Map.Map Int [Int]
convertMap sigs ids = Map.map (map (convertID ids)) $ Map.mapKeys (convertID ids) sigs

convertVarMap :: Map.Map String String -> Map.Map String Int -> Map.Map Int Int
convertVarMap sigs ids = Map.map (convertID ids) $ Map.mapKeys (convertID ids) sigs


makeIDMap' :: Map.Map String [String] -> Map.Map String [String] -> Map.Map String Int
makeIDMap' s sigs = Map.fromList $ [("random", (-4)), ("weight", (-3)), ("*", (-2)), ("true", 0), ("false", 1)] ++ (zip values [2..]) --siglist ++ idlist
                       where
                           values = (Map.keys sigs) ++ (foldl (++) [] [Map.findWithDefault [] set s | set <- Map.keys s]) ++ (Map.keys s)
                           siglist = zip (Map.keys sigs) [3..]
                           idlist = foldl (++) [] [[(val,start set + id) | (val,id) <- zip (Map.findWithDefault [] set s) [1..]] | set <- Map.keys s]
                           start target = (length $ Map.keys sigs) + (sum $ map length [Map.findWithDefault [] set s | set <- takeWhile (/= target) $ Map.keys s] ) + 2

makeIDMap :: Context -> Map.Map String Int
makeIDMap ctx@(GameContext {sets=s, signatures=sigs}) = makeIDMap' s sigs

makeReverseIDMap :: Context -> Map.Map Int String
makeReverseIDMap ctx = Map.fromList [(v,k) | (k,v) <- Map.assocs $ makeIDMap ctx]

makeMap :: Ord k => (k -> a) -> [k] -> Map.Map k a
makeMap f values = Map.fromList [(k, f k) | k <- values]

formatCall :: String -> [String] -> String
formatCall name args = name ++ "(" ++ (intercalate "," args) ++ ")"

toOutput :: String -> String
toOutput ('s':'t':'r':':': str) = str
toOutput s = s

showOutput :: String -> IO ()
showOutput "" = return ()
showOutput s = putStrLn s

          