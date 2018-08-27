{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}

module GamePlay where

import BaseTypes
import Baltag
import AbstractActions
import ActionCompiler
import BaltagExecution
import Agents
import AbstractActionExecution
import Planning
import qualified Data.Map as Map
import Data.List.Split
import Data.List
import Control.Monad
import Debug.Trace
import Control.Monad.Random
import Control.Monad.Random.Class


data PhaseMode = Mandatory | Optional
               deriving (Show,Eq,Ord)

data PhaseDefinition a = Phase { name :: String, turns :: Int, valid_moves :: [String], mode :: PhaseMode, nextPhase :: (String,[a]) }
                   deriving (Show,Eq,Ord)
                   


toGameInt :: Context -> Game String -> Game Int
toGameInt _ [] = []
toGameInt ctx ((phase,turns,actions,mode,(next,args)):xs) = (phase,turns,actions,mode,(next,map (strToInt ctx) args)):(toGameInt ctx xs)

optimizeBinding :: Context -> (String, Term String) -> (Int, Term Int)
optimizeBinding ctx (var,val) = (strToInt ctx var, replaceIndexedPropertiesT ctx $ optimizeTerm ctx val)

toGoalsInt :: Context -> Goals String -> Goals Int
toGoalsInt ctx goals = map (\(bindings,a,b) -> (map (optimizeBinding ctx) bindings,replaceIndexedPropertiesP ctx $ optimizePredicate ctx a, replaceIndexedPropertiesP ctx $ optimizePredicate ctx b)) goals

toGameDefInt :: Context -> (Goals String, Game String) -> (Goals Int, Game Int)
toGameDefInt ctx (goals,game) = (toGoalsInt ctx goals, toGameInt ctx game)

indexBinding :: Context -> (String, Term String) -> (String, Term String)
indexBinding ctx (var,val) = (var,replaceIndexedPropertiesT ctx val)

indexGameDef :: Context -> (Goals String, Game String) -> (Goals String, Game String)
indexGameDef ctx (goals, game) = (map (\(bindings,a,b) -> (map (indexBinding ctx) bindings, replaceIndexedPropertiesP ctx a, replaceIndexedPropertiesP ctx b)) goals, game)

emptyPhase = Phase { name="", turns=0, valid_moves =[], mode=Optional, nextPhase=("",[]) }

toMode "optional" = Optional
toMode _ = Mandatory

tomap :: (Goals a, Game a) -> Map.Map String (PhaseDefinition a)
tomap (goals,game) = Map.fromList [(nm, Phase { name=nm, turns=ts, valid_moves=actions, mode = toMode m, nextPhase=nxt}) | (nm,ts,actions,m,nxt) <- game]


play :: PlanningDomain a b c d x => Context -> a -> (Goals d, Game d) -> [(String,String,[String])] -> Map.Map String (AbstractAction d) -> MOptions -> IO ([a],String)
play ctx state game players actionmap opts = do 
                                            agents <- mapM (makeAgent (fst game) ctx opts) players
                                            play' ctx (state,"") (tomap game) agents (propertyValue ctx state (getPhaseName ctx) [(getGameName ctx)]) actionmap opts


play' :: PlanningDomain a b c d x => Context -> (a,String) -> Map.Map String (PhaseDefinition d) -> [Agent c b d] -> String -> Map.Map String (AbstractAction d) -> MOptions -> IO ([a],String)
play' ctx (state,output) game players "Done" _ _ = return ([state],output)
play' ctx (state,output) game players phaseName actionmap opts = do
                                                 putStrLn $ "current phase: " ++ (show phaseName)
                                                 if Map.member phaseName game then do
                                                     let phase = Map.findWithDefault emptyPhase phaseName game
                                                     let (actionname,args) = nextPhase phase
                                                     let action = Map.findWithDefault nop actionname actionmap
                                                     let argnames = getArgNames action
                                                     let argassignment = Map.fromList $ zip argnames args
                                                     let compiled = assignArgs action ctx argassignment $ showCall ctx actionname args
                                                     (phaseState,phaseOutput,newplayers) <- playPhase ctx state phase players (turns phase) actionmap opts
                                                     let (newstate,newoutput) = head $ executeAction phaseState compiled
                                                     let newphase = propertyValue ctx newstate (getPhaseName ctx) [(getGameName ctx)]
                                                     --putStrLn $ "output: \n" ++ phaseOutput ++ newoutput
                                                     play' ctx (newstate,output ++ phaseOutput ++ newoutput) game (map resetPlayer newplayers) newphase actionmap opts  
                                                 else
                                                     return $! ([state],output)
                                               
                                               
playPhase :: PlanningDomain a b c d x =>  Context -> a -> PhaseDefinition d -> [Agent c b d] -> Int -> Map.Map String (AbstractAction d) -> MOptions -> IO (a,String,[Agent c b d])
playPhase ctx state phase players 0 actionmap _ = return (state,"",players)
playPhase ctx state phase players turns actionmap opts = do
                                                       (newstate,newoutput,newplayers) <- playRound ctx state phase players (length players) actionmap opts
                                                       (resultstate,resultoutput,resultplayers) <- playPhase ctx newstate phase newplayers (turns - 1) actionmap opts
                                                       return $! (resultstate,newoutput ++ resultoutput,resultplayers)

moveArgAssignments :: PlanningDomain a b c d x => Context -> String -> AbstractAction d -> String -> [b]
moveArgAssignments ctx player action name = if null argnames then [assignArgsExtra action ctx (head $ getArgNames action) player Map.empty $ showCall ctx name [player]]
                                       else [assignArgsExtra action ctx (head $ getArgNames action) player (Map.fromList $ zip argnames args) $ showCall ctx name args | args <- sequence [getValues ctx arg | arg <- argtypes] ]
                                          where
                                              argnames = tail $ getArgNames action
                                              argtypes = tail $ getArgTypes action
                                                                
getArgAssignments ctx player action = if null argnames then [argmap]
                                       else [Map.fromList $ (head $ getArgNames action, player):(zip argnames args) | args <- sequence [getValues ctx arg | arg <- argtypes] ]
                                          where
                                              argnames = tail $ getArgNames action
                                              argtypes = tail $ getArgTypes action
                                              argmap = Map.singleton (head $ getArgNames action) player
                                              
replaceN :: [a] -> Int -> a -> [a]
replaceN list at newitem = pre ++ (newitem:newpost)
                        where
                           (pre,post) = splitAt at list
                           newpost = tail post
                           
unsafeIndex :: Eq a => a -> [a] -> Int
unsafeIndex item lst = extract $ elemIndex item lst
                    where
                       extract (Just i) = i
                       extract Nothing = 0
 
playRound :: PlanningDomain a b c d x => Context -> a -> PhaseDefinition d -> [Agent c b d] -> Int -> Map.Map String (AbstractAction d) -> MOptions -> IO (a,String,[Agent c b d])
playRound ctx state phase players 0 actionmap _ = return $! (state,"",players)
playRound ctx state phase players pnr actionmap opts = do
                                                      let currentPlayer = players!!(length players - pnr)
                                                      let moves = map (\n -> (Map.findWithDefault nop n actionmap, n)) $ valid_moves phase
                                                      let extra = if (mode phase) == Optional then [(assignArgs nop ctx Map.empty "nothing","nothing")] else []
                                                      let actions = extra ++ (concat $! map (\(a,n) -> map (\act -> (act,n)) $ moveArgAssignments ctx (show currentPlayer) a n) moves)
                                                      
                                                      let applicableActions = filter (\((a,n),i) -> applicable state a) $ zip actions [0..]
                                                      --putStrLn $ (show currentPlayer) ++ " has " ++ (show $ length applicable) ++ " options"
                                                      --putStrLn $ "trimmed: " ++ (show ((length actions) - (length applicable)))
                                                      --if (null applicable) || (not $ null applicable) then do
                                                      --    putStrLn (show $ length applicable)
                                                      if null applicableActions then
                                                          playRound ctx state phase players (pnr - 1) actionmap opts
                                                      else do
                                                          (move,newplayer) <- turn currentPlayer state (map (fst.fst) applicableActions) opts
                                                          let mindex = unsafeIndex move $ map (fst.fst) applicableActions
                                                          let argindex = snd $ applicableActions!!mindex
                                                          let name = snd $ fst $ applicableActions!!mindex
                                                          --let args = (if (mode phase) == Optional then [ Map.empty ] else []) ++ (concat $ map (getArgAssignments ctx (show currentPlayer)) (map fst moves))
                                                          putStrLn $ (show currentPlayer) ++ " does: " ++ arepr move
                                                          -- ++ " with args: " ++ (show (args!!argindex)) ++ " (" ++ (show argindex) ++ ")"
                                                          let (newstate,output) = head $ executeAction state move
                                                          let newplayers = replaceN players (length players - pnr) newplayer
                                                          showOutput output
                                                          playRound ctx newstate phase newplayers (pnr - 1) actionmap opts
                                                 where 
                                                    ids = makeReverseIDMap ctx
                                                      
                                                    