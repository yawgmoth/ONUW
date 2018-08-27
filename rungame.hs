{-# LANGUAGE QuasiQuotes #-}
module Main where

import BaseTypes
import GameParser
import qualified System.Environment as E
import Text.ParserCombinators.Parsec
import Control.Monad
import Baltag
import AbstractActions
import ActionCompiler
import BaltagExecution
import AbstractActionParser
import qualified Data.ByteString as B
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.List
import Data.Char
import Debug.Trace
import Data.Either
import Data.Function
import Data.List.Split
import Control.Parallel.Strategies
import Agents
import GamePlay
import Planning
import System.Console.Docopt

extractResult (Right r) = r

patterns :: Docopt
patterns = [docoptFile|usage.txt|]

getArgOrExit = getArgOrExitWith patterns

extractArg (Just x) = x
extractArg Nothing = "default"

getArgOrDefault args opt = extractArg $ args `getArg` opt

 

main :: IO()
main = do
          args1 <- parseArgsOrExit patterns =<< E.getArgs
          fname <- args1 `getArgOrExit` (argument "input")
          let scount = (args1 `getArgOrDefault` (shortOption 's'))
          let al = (args1 `getArgOrDefault` (shortOption 'a'))
          let iters = (args1 `getArgOrDefault` (shortOption 'n'))
          let comm = (args1 `getArgOrDefault` (shortOption 'c'))
          input <- processFile fname
          processParseResult input MainOptions { suspicions=read scount :: Int, alpha = read al :: Float, iterations = read iters :: Int, commitment = read comm :: Float }
          
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
                                      let ids = makeReverseIDMap ctx
                                      doExecute execute ctx [init] (Map.fromList actions) game opts


                              

  
actionName :: String -> String  
actionName ('s':'u':'s':'p':'e':'c':'t':'(':xs) = actionName $ intercalate " " $ tail (splitOn " " xs)
actionName name = name

actionDecorations ('s':'u':'s':'p':'e':'c':'t':'(':xs) = head (splitOn ")" xs):(actionDecorations $ intercalate " " $ tail (splitOn " " xs))
actionDecorations name = []

decorate action [] = action
decorate action (x:xs) = Learn (decorate action xs) x

appearanceStats worlds = (show $ length worlds) ++ " worlds, with appearances of size: " ++ (show $ map ((Map.foldl (accum) [])) $ map appearanceB worlds)


strreplace a b t = t
          
doExecute [] _ _ _ _ _ = putStrLn "Done."
doExecute (x:xs) ctx states actionmap game opts = do
                                                  newstates <- performAction x ctx states actionmap game opts
                                                  doExecute xs ctx newstates actionmap game opts
                                                

performAction :: ExecutionType -> Context -> [PointedModel] -> Map.Map String (AbstractAction String) -> (Goals String,Game String) -> MOptions -> IO [PointedModel]
performAction (Query what) ctx states actionmap game opts = do
                                                                let query = compilePredicate what ctx
                                                                putStrLn $ "query: " ++ (show what) ++ " is \n    " ++ (show $ (head states) `canExecute` query)
                                                                return states
performAction (QueryWhich var set what) ctx states actionmap game opts = 
                                                                   do
                                                                      let values = getValues ctx set
                                                                      queryWhich ctx var values what states
                                                                      return states
performAction (QueryEach var set what) ctx states actionmap game opts = 
                                                                   do
                                                                      let values = getValues ctx set
                                                                      queryEach ctx var values what states
                                                                      return states
performAction (ExecPrint what args) ctx states actionmap game opts 
                                       | what == "facts" = do
                                                               let sids = rids ctx
                                                               putStrLn $ "State of the world is now: \n" ++ (intercalate "\n\nor:\n" $ map (\s -> intercalate ", " (map (toString sids) $ factList s)) states) ++ "\n"
                                                               return states
                                       | what == "model" = do 
                                                               let sids = rids ctx
                                                               putStrLn $ "The world is now: \n" ++ (intercalate "\nor:\n" $ map (toString sids) states) ++ "\n"
                                                               return states
                                       | what == "appearance" = do
                                                                   putStrLn $ "Not implemented yet"
                                                                   return states
                                       | what == "stats" = do 
                                                               putStrLn $ "Have " ++ (show $ Set.size $ fact $ head states) ++ " facts"
                                                               putStrLn $ intercalate "\n" [a ++" sees " ++ (appearanceStats $ Map.findWithDefault [] a (appearanceB $ head states)) ++ " worlds\n" | a <- actors ctx]
                                                               return states
                                       | otherwise = do
                                                        let (aname,aargs) = extractResult $ parseActionCall $ what
                                                        let paction = Map.findWithDefault nop aname actionmap
                                                        let pargnames = getArgNames paction
                                                        let pargassignment = Map.fromList $ zip pargnames aargs
                                                        let pcompiled = compile paction ctx pargassignment
                                                        let sids = rids ctx
                                                        putStrLn $ show paction
                                                        putStrLn $ toString sids pcompiled
                                                        putStrLn $ intercalate "\n" ["appears to " ++ a ++" as:\n " ++ (intercalate " \nor\n " $ map (toString sids) $ alternatives a pcompiled) ++ "\n\n" | a <- actors ctx]
                                                        putStrLn $ "pre: " ++ (toString sids $ pre pcompiled)
                                                        putStrLn $ "applicable: " ++ (show $ interprets (head states) $ pre pcompiled)
                                                        return states
performAction (Execute actionname args decorations) ctx states actionmap game opts = do
                                                                    let action = Map.findWithDefault nop actionname actionmap
                                                                    let argnames = getArgNames action
                                                                    let argassignment = Map.fromList $ zip argnames args
                                                                    let compiled = compile action ctx argassignment
                                                                    let decorated = decorate compiled decorations
                                                                    putStrLn $ "Executing " ++ (intercalate " " $ map (\a -> (a ++ " suspects ")) decorations) ++ actionname ++ "(" ++ (intercalate ", " args) ++ ")"
                                                                    let result = concat [execute s decorated | s <- states]
                                                                    let newstates = map fst result
                                                                    let outp = intercalate "" $ map snd result
                                                                    putStrLn outp
                                                                    return newstates
performAction (Plan goal actions) ctx states actionmap game opts = do
                                                              putStrLn $ "Planning a trajectory to " ++ (show goal)
                                                              let actionset = Set.fromList actions
                                                              let actionfilter k _ = Set.member k actionset
                                                              let validActions = if null actions then actionmap else Map.filterWithKey actionfilter actionmap 
                                                              let goalP = compilePredicate goal ctx
                                                              let sequence = plan states goalP (toActionList validActions ctx $ suspicions opts)
                                                              let formatH (a,b,c) = (c,b)
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
                                                              putStrLn "Not implemented yet"
                                                              return states
                                                                   
performAction (Play args) ctx states actionmap game opts = do
                                                               (playstate,playoutput) <- play ctx (head states) game args actionmap opts
                                                               putStrLn playoutput
                                                               return playstate
                                                               
                                                  
queryWhich :: Context -> String -> [String] -> Predicate String -> [PointedModel] -> IO ()
queryWhich _ _ [] _ _ = putStrLn "None"
queryWhich ctx varname (v:vs) pred states = if holds then putStrLn v else queryWhich ctx varname vs pred states
                                     where
                                         holds = and [canExecute state query | state <- states]
                                         query = compilePredicate (resolveVarsPredicate (Map.singleton varname v) pred) ctx

queryEach :: Context -> String -> [String] -> Predicate String -> [PointedModel] -> IO ()
queryEach _ _ [] _ _ = putStrLn "None"
queryEach ctx varname (v:vs) pred states = do
                                               if holds then putStrLn (v ++ ": True") else putStrLn (v ++ ": False")
                                               queryEach ctx varname vs pred states
                                     where
                                         holds = and [canExecute state query | state <- states]
                                         query = compilePredicate (resolveVarsPredicate (Map.singleton varname v) pred) ctx
                                         