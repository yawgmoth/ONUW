{-# LANGUAGE QuasiQuotes #-}
module Main where

import BaseTypes
import GameParser
import qualified System.Environment as E
import Text.ParserCombinators.Parsec
import Control.Monad
import Baltag
import AbstractActions
import AbstractActionExecution
import ActionCompiler
import BaltagExecution
import AbstractActionParser
import qualified Data.ByteString as B
import qualified Data.Map as Map
import qualified Data.Array.IArray as Array
import qualified Data.Array.Unboxed as UArray
import qualified Data.Set as Set
import Data.List
import Data.Char
import Debug.Trace
import Data.Either
import Data.Function
import Data.List.Split
import Control.Parallel.Strategies
import GamePlay
import Agents
import Planning
import System.IO
import System.Console.Docopt


extractResult (Right r) = r
extractError (Left l) = l

isError (Right _) = False
isError (Left _) = True


patterns :: Docopt
patterns = [docoptFile|usage.txt|]

getArgOrExit = getArgOrExitWith patterns

extractArg (Just x) = x
extractArg Nothing = "default"

getArgOrDefault args opt = extractArg $ args `getArg` opt

 
main :: IO()
main = do
          hSetBuffering stdout LineBuffering
          args1 <- parseArgsOrExit patterns =<< E.getArgs
          fname <- args1 `getArgOrExit` (argument "input")
          let scount = (args1 `getArgOrDefault` (shortOption 's'))
          let al = (args1 `getArgOrDefault` (shortOption 'a'))
          let iters = (args1 `getArgOrDefault` (shortOption 'n'))
          let comm = (args1 `getArgOrDefault` (shortOption 'c'))
          --args <- E.getArgs
          --let (scount,fname) = if length args > 2 then
          --                        if args!!1 == "-s" then (read (args!!2) :: Int,head args) else
          --                        if args!!0 == "-s" then (read (args!!1) :: Int,args!!2) else
           --                       (1,head args)
           --                  else (1,head args)
          input <- processFile fname
          processParseResult input MainOptions { suspicions=read scount ::Int, alpha = read al :: Float, iterations = read iters :: Int, commitment = read comm :: Float }
          
ltrim :: String -> String
ltrim = dropWhile isSpace
   
   
isComment :: String -> Bool
isComment s = isPrefixOf "//" $ ltrim s
          
processFile fname = do
          content <- readFile fname
          let lines = splitOn "\n" content
          let nonComments = filter (not . isComment) lines
          return $ parse parseGame fname $ intercalate "\n" nonComments

processParseResult (Left err) _ = putStrLn $ show err
processParseResult (Right presult) opts = do
                                      let (ctx,init,execute,actions,game) = presult
                                      let pm = makeIndex $ fromPMInt init
                                      let newctx = (contextA pm)
                                      let fixedActions = map (\(n,act) -> (n,optimizeAction ctx $ replaceIndexedProperties newctx act)) actions
                                      doExecute execute newctx [pm] (Map.fromList fixedActions) (toGameDefInt newctx game) opts

  
actionName :: String -> String  
actionName ('s':'u':'s':'p':'e':'c':'t':'(':xs) = actionName $ intercalate " " $ tail (splitOn " " xs)
actionName name = name

actionDecorations ('s':'u':'s':'p':'e':'c':'t':'(':xs) = head (splitOn ")" xs):(actionDecorations $ intercalate " " $ tail (splitOn " " xs))
actionDecorations name = []

decorate action [] = action
decorate action (x:xs) = SuspectAction x $ decorate action xs

showOutput :: String -> IO ()
showOutput "" = return ()
showOutput s = putStrLn s

strreplace a b t = t



doExecute :: [ExecutionType] -> Context -> [PointedModelA Int IArray] -> Map.Map String (AbstractAction Int) -> (Goals Int, Game Int) -> MOptions -> IO ()
doExecute [] _ _ _ _ _ = putStrLn "Done."
doExecute (exec:xs) ctx states actionmap game opts = do
                                                     newstates <- performAction exec ctx states actionmap game opts
                                                     doExecute xs ctx newstates actionmap game opts
                                                     

formatFact :: String ->  String -> [String] -> String -> String
formatFact prop prefix args value = prefix ++ "\n" ++ prop ++ "(" ++ (intercalate ", " args) ++ ") = " ++ value

formatProperty :: String -> String -> Map.Map [String] String -> String
formatProperty prefix prop values = prefix ++ (Map.foldlWithKey (formatFact prop) "" values)
                                                     
formatFacts :: Map.Map String (Map.Map [String] String) -> String
formatFacts facts = Map.foldlWithKey formatProperty "" facts

formatPropertyIndex :: Context -> SArray -> String -> [String]
formatPropertyIndex ctx index prop = map (\(a,v) -> (prop ++ "(" ++ a ++ ") = " ++ v)) values
                                  where
                                      sig = Map.findWithDefault [] prop $ signatures ctx
                                      args = getSet ctx (sig!!1)
                                      values = filter (\(a,v) -> v /= "") $ map (\a -> (a, (Array.!) index (toIndex ctx prop,toIndex ctx a))) args
                                      

formatIndex :: Context -> SArray -> String
formatIndex ctx index = intercalate "\n" $ concat $ map (formatPropertyIndex ctx index) $ indexed ctx


                                                     
appearanceStats worlds = (show $ length worlds) ++ " worlds" --, with appearances of size: " ++ (show $ map ((Map.foldl (accum) [])) $ map appearanceAMap worlds)

performAction :: ExecutionType -> Context -> [PointedModelA Int IArray] -> Map.Map String (AbstractAction Int) -> (Goals Int,Game Int) -> MOptions -> IO [PointedModelA Int IArray]
performAction (Query what) ctx states actionmap game opts = do
                                                                      let fixedQuery = replaceIndexedPropertiesP ctx what
                                                                      putStrLn $ "query: " ++ (show (optimizePredicate ctx fixedQuery)) ++ "\n    "
                                                                      putStrLn $ "query: " ++ (show fixedQuery) ++ " is \n    " ++ (show $ (head states) `interpretsA` (optimizePredicate ctx fixedQuery))
                                                                      return states
performAction (Quality what) ctx states actionmap game opts = do
                                                                      let fixedQuery = replaceIndexedPropertiesP ctx what
                                                                      putStrLn $ "query: " ++ (show (optimizePredicate ctx fixedQuery)) ++ "\n    "
                                                                      putStrLn $ "query: " ++ (show fixedQuery) ++ " is \n    " ++ (show $ (head states) `qualityA` (optimizePredicate ctx fixedQuery))
                                                                      return states
performAction (QueryWhich var set query) ctx states actionmap game opts = 
                                                                   do
                                                                      let values = getValues ctx set
                                                                      let fixedQuery = replaceIndexedPropertiesP ctx query
                                                                      let matches = filter (\v -> (head states) `interpretsA` (optimizePredicate ctx $ resolveVarsPredicate (Map.singleton var v) fixedQuery)) values
                                                                      putStrLn $ "query: Which " ++ var ++ " in " ++ set ++ ":\n " ++ (show fixedQuery) ++ "\n   " ++ (if null matches then "None." else head matches)
                                                                      return states
performAction (QueryEach var set query) ctx states actionmap game opts = 
                                                                   do
                                                                      let values = getValues ctx set
                                                                      let fixedQuery = replaceIndexedPropertiesP ctx query
                                                                      let matches = map (\v -> (v,(head states) `interpretsA` (optimizePredicate ctx $ resolveVarsPredicate (Map.singleton var v) fixedQuery))) values
                                                                      putStrLn $ "query: Each " ++ var ++ " in " ++ set ++ ":\n " ++ (show fixedQuery)
                                                                      putStrLn $ intercalate "\n" [ "   " ++ v ++ ": " ++ (show t) | (v,t) <- matches]
                                                                      return states
performAction (ExecPrint what args) ctx states actionmap game opts 
                                       | what == "facts" = do
                                                               putStrLn "The world is now:"
                                                               let state = fromPMAInt $ head states
                                                               putStrLn $ formatFacts $ factsA $ state
                                                               putStrLn "------------------------------"
                                                               putStrLn $ formatIndex (contextA $ state) (indexedA $ state)
                                                               return states
                                       | what == "model" = do 
                                                               let state = fromPMAInt $ head states
                                                               putStrLn $ formatFacts $ factsA $ state
                                                               putStrLn $ intercalate "\n" ["appears to " ++ a ++" as:\n " ++ (intercalate " \nor\n " $ map (formatFacts . factsA) $ Map.findWithDefault [] a (appearanceAMap $ state)) ++ "\n\n" | a <- actors ctx]
                                                               return states
                                       | what == "appearance" = do
                                                                   showAppearance (fromPMAInt $ head states) args 0
                                                                   return states
                                       | what == "stats" = do 
                                                               putStrLn $ "Have " ++ (show $ Map.size $ factsA $ head states) ++ " facts"
                                                               putStrLn $ intercalate "\n" [a ++" sees " ++ (appearanceStats $ Map.findWithDefault [] a (appearanceAMap $ fromPMAInt $ head states)) ++ "\n" | a <- actors ctx]
                                                               return states
                                       | what == "index" = do
                                                               putStrLn "Indexed properties:"
                                                               putStrLn $ show $ indexed ctx
                                                               putStrLn "Has index of size:"
                                                               putStrLn $ show $ Array.bounds $ indexedA $ head states
                                                               return states
                               {-        | what == "cpp" = do
                                                       let aname = head args
                                                       let action = Map.findWithDefault nop aname actionmap
                                                       putStrLn $ toCppAction ctx aname action
                                                       return states -}
                                                       
                                       | otherwise = do
                                                       let aname = what
                                                       let aargs = args                                                           
                                                       let action = Map.findWithDefault nop aname actionmap
                                                       let argnames = map fst $ getActionArgs action
                                                       let argassignments = Map.fromList $ zip argnames $ map (strToInt ctx) aargs
                                                       let resolved = resolveArgs ctx argassignments action $ formatCall aname aargs
                                                       putStrLn $ show resolved
                                                       putStrLn $ "Can execute:" ++ (show $ canExecuteA (head states) resolved)
                                                       putStrLn $ "Requirements: " ++ (show $ getRequirements resolved)
                                                       putStrLn $ "Changes: " ++ (show $ getChanges resolved)
                                                       return states
performAction (Execute actionname args decorations) ctx states actionmap game opts = do
                                                                    putStrLn $ "Executing " ++ (intercalate " " $ map (\a -> (a ++ " suspects ")) decorations) ++ actionname ++ "(" ++ (intercalate ", " args) ++ ")"
                                                                    let action = Map.findWithDefault nop actionname actionmap
                                                                    let argnames = map fst $ getActionArgs action
                                                                    let argassignments = Map.fromList $ zip argnames $ map (strToInt ctx) args
                                                                    let resolved = resolveArgs ctx argassignments action $ formatCall actionname args
                                                                    let decorated = decorate resolved $ map (strToInt ctx) decorations
                                                                    let result = concat [executeA s decorated | s <- states]
                                                                    let newstates = map fst result
                                                                    let outp = intercalate "" $ map snd result
                                                                    putStrLn outp
                                                                    return newstates
performAction (Plan goal actions) ctx states actionmap game opts = do
                                                              let fixedGoal = replaceIndexedPropertiesP ctx goal
                                                              putStrLn $ "Planning a trajectory to " ++ (show fixedGoal)
                                                              putStrLn $ "Requirements for goal:" ++ (show $ getReferences fixedGoal)
                                                              let actionset = Set.fromList actions
                                                              let actionfilter k _ = Set.member k actionset
                                                              let validActions = if null actions then actionmap else Map.filterWithKey actionfilter actionmap 
                                                              let allActions = actionList 1 (generateOptions ctx validActions) ctx
                                                              let sequence = plan states (optimizePredicate ctx fixedGoal) allActions
                                                              let formatH (a,b,c) = (c,b)
                                                              --putStrLn $ intercalate "\n" $ map (\(a,n) -> (n ++ ": " ++ (show $ getRequirements a) ++ " -> " ++ (show $ getChanges a))) allActions
                                                              --putStrLn $ show $ map (formatH) $ ostariHeuristic allActions [goal]
                                                              if not $ null sequence then do
                                                                   let solution = head sequence
                                                                   putStrLn "Solution found"
                                                                   let actions = snd solution
                                                                   let output = snd $ fst solution
                                                                   let newstates = [fst $ fst solution]
                                                                   putStrLn output
                                                                   putStrLn $ "For example " ++ (intercalate ", " actions)
                                                                   return newstates
                                                              else do
                                                                   putStrLn "No solution found"
                                                                   return states
                                                                   
performAction (PlanAgent goal actions agent) ctx states actionmap game opts = do
                                                              let fixedGoal = replaceIndexedPropertiesP ctx goal
                                                              putStrLn $ "Planning a trajectory to " ++ (show fixedGoal)
                                                              putStrLn $ "Requirements for goal:" ++ (show $ getReferences fixedGoal)
                                                              let actionset = Set.fromList actions
                                                              let actionfilter k _ = Set.member k actionset
                                                              let validActions = if null actions then actionmap else Map.filterWithKey actionfilter actionmap 
                                                              let allActions = actionList 1 (generateAgentOptions ctx validActions $ strToInt ctx agent) ctx
                                                              let sequence = plan states (optimizePredicate ctx fixedGoal) allActions
                                                              let formatH (a,b,c) = (c,b)
                                                              --putStrLn $ intercalate "\n" $ map (\(a,n) -> (n ++ ": " ++ (show $ getRequirements a) ++ " -> " ++ (show $ getChanges a))) allActions
                                                              --putStrLn $ show $ map (formatH) $ ostariHeuristic allActions [goal]
                                                              if not $ null sequence then do
                                                                   let solution = head sequence
                                                                   putStrLn "Solution found"
                                                                   let actions = snd solution
                                                                   let output = snd $ fst solution
                                                                   let newstates = [fst $ fst solution]
                                                                   putStrLn output
                                                                   putStrLn $ "For example " ++ (intercalate ", " actions)
                                                                   return newstates
                                                              else do
                                                                   putStrLn "No solution found"
                                                                   return states
                                                                   
performAction (Play args) ctx states actionmap game opts = do
                                                               (playstate,playoutput) <- play ctx (head states) game args actionmap opts
                                                               putStrLn playoutput
                                                               return playstate 
                                                               {-(playstate,playoutput) <- play ctx (head states) (indexGameDef ctx game) args actionmap
                                                               putStrLn playoutput
                                                               return playstate -}
                                                               
performAction (Lock properties) ctx states actionmap game opts = do
                                                               return states -- $ map (performLocking ctx properties) states
                                                               
performAction (Prompt) ctx states actionmap game opts = do 
                                                            putStr "> "
                                                            x <- getLine
                                                            return states
                                                               
                                                                   

showAppearance :: PointedModelA String SArray -> [String] -> Int -> IO ()
showAppearance state [] n = return ()
showAppearance state (actor:actors) n = do
                                          let app = getAppearance state actor
                                          foldl (>>) (putStrLn $ (replicate n ' ') ++ actor ++ " sees (" ++ (show $ length app)++ "):")  [ (putStrLn $ (replicate n ' ') ++ (formatFacts $ factsA a) ++ "\n" ++ (formatIndex (contextA a) (indexedA a))) >> showAppearance a actors (n+3) | a <- app]
                                          return ()

                                         