module Agents where

import Control.Monad.State
import Control.Monad.Random
import Control.Monad.Random.Class
import Data.List.Split
import Data.List
import Data.Ord
import qualified Data.Map as Map
import Baltag
import BaltagExecution
import Debug.Trace
import Planning hiding (State)
import ActionCompiler
import AbstractActions
import BaseTypes


type Goals a = [([(a,Term a)],Predicate a, Predicate a)]
type Game a = [(String,Int,[String],String,(String,[a]))]

data RandomAgent = RA StdGen

data Commitment = Fanatical | Balanced Float | Capricious

data IntentionalAgent a b c = IA [([(c,Term c)],a,a)] (a, [b], Quality, StdGen) Commitment

data CountingAgent = CA Int


data Agent a b c = RAgent RandomAgent String
            | IAgent (IntentionalAgent a b c) String Context
            | CAgent CountingAgent String
            | NAgent String
            | IOAgent String
       
instance Show (Agent a b c) where
  show (RAgent rando name) = name
  show (IAgent _ name _) = name
  show (CAgent (CA cnt) name) = name ++ " at " ++ (show cnt)
  show (NAgent name) = name
  show (IOAgent name) = name
  
compileAll :: PlanningDomain a b c d x => Context -> String -> ([(d,Term d)],Predicate d, Predicate d) -> ([(d, Term d)], c, c)
compileAll ctx name (bindings,a,b) = (newb, assignStringArgToPredicate ctx a "self" name, assignStringArgToPredicate ctx b "self" name)
                                   where
                                      newb = map (\(var,val) -> (var,resolveBindingsString ctx val "self" name)) bindings
  
makeAgent :: PlanningDomain a b c d x => Goals d -> Context -> MOptions -> (String,String,[String]) -> IO (Agent c b d)
makeAgent goals ctx opts (name,agent,args) = makeAgent' goals' name agent args ctx opts
                where
                  goals' = map (compileAll ctx name) goals
                  
makeAgent' _ name "random" _ _ _ = do
                              gen <- newStdGen
                              return $ RAgent (RA gen) name
makeAgent' goals name "fanatical" _ ctx _ = do
                                           gen <- newStdGen
                                           return $ IAgent (IA goals (defaultgoal, [], (False,zero), gen) Fanatical) name ctx
makeAgent' goals name "balanced" [] ctx opts = do
                                           gen <- newStdGen
                                           return $ IAgent (IA goals (defaultgoal, [], (False,zero), gen) (Balanced $ commitment opts)) name ctx
makeAgent' goals name "balanced" args ctx opts = do
                                           gen <- newStdGen
                                           return $ IAgent (IA goals (defaultgoal, [], (False,zero), gen) (Balanced $ ((read $ head args) :: Float))) name ctx
makeAgent' goals name "capricious" _ ctx _ = do
                                           gen <- newStdGen
                                           return $ IAgent (IA goals (defaultgoal, [], (False,zero), gen) Capricious) name ctx
makeAgent' _ name "counting" _ _ _ = return $ CAgent (CA 0) name
makeAgent' _ name "lazy" _ _ _ = return $ NAgent name
makeAgent' _ name "io" _ _ _ = return $ IOAgent name
          
moveIndex :: (RandomGen g) => Int -> Rand g Int
moveIndex m = getRandomR (0,m)

countingMove :: CountingAgent -> [a] -> (a,Int)
countingMove (CA n) (m:mvs) = (m,n+1)
           
randomMove :: (RandomGen g) => [a] -> Rand g a
randomMove moves = do
                    index <- moveIndex (length moves - 1)
                    return $ moves!!index
                    
planMoves :: PlanningDomain a b c d x => a -> [b] -> c -> [b]
planMoves gs moves prop = mytrace Agents ("have moves: " ++ (show $ length moves)) $ calculateLimitedPlan [gs] prop moves 10

reconsider _ plan newplan (_,qual) (_,newqual) alpha = (alpha * newqual) > qual
                                           -- (fromIntegral $ length newplan) < alpha * (fromIntegral $length plan)

applies :: PlanningDomain a b c d x => a -> (c, c) -> Bool
applies gs (p,_) = interpretsCondition gs p

reached :: PlanningDomain a b c d x => a -> (c, c) -> Bool
reached gs (_,p) = interpretsCondition gs p

-- trace ("vars: " ++ (show $ map (\(var,val) -> (toDebug gs ctx var,toDebug gs ctx val)) bvals) ++ "\n" ++ (show c) ++ ": " ++ (show g) ) $
resolveBindings :: PlanningDomain a b c d x => Context -> a -> [Int] -> ([(d,Term d)],c,c)  -> (c,c)
resolveBindings ctx gs _ ([],cond,goal) = (cond,goal)
resolveBindings ctx gs vals (bindings,cond,goal) = (c,g)
                                           where
                                              bvals = map (\((var,expr),ind) -> (var,getBindingValue ctx gs expr ind)) $ zip bindings vals
                                              valmap = Map.fromList bvals
                                              (c,g) = (resolveBindingsP ctx cond valmap,resolveBindingsP ctx goal valmap)
                                               


bestIntention :: PlanningDomain a b c d x => String -> a -> [([(d,Term d)],c, c)] -> [b] -> Context -> StdGen -> MOptions -> ([b],c,Quality,StdGen)
bestIntention name gs goals moves ctx gen opts = if null applicable || null plans' then ([],defaultgoal,(False,zero),gen) else best_plan  -- minimumBy (comparing $ length . fst) valid_plans
                            where
                                goals' = map (resolveBindings ctx gs (randoms gen)) goals
                                applicable' = filter (applies gs) goals' -- show $ map (applies gs) goals
                                applicable = mytrace Agents ("available goals for " ++ name ++ ": " ++ (show $ length applicable') ++ (intercalate "\n" $ map (\g -> (show g) ++ ": " ++ (show $ applies gs g)) goals')  ++ (show $ map (reached gs) goals'))  applicable'
                                -- plans = map (\(_,g) -> (planMoves gs moves g,g)) applicable
                                -- valid_plans = mytrace Agents ("found plans: " ++ (show $ map (length.fst) plans)) $ filter (not . null . fst) plans
                                plans' = calculatePotentialPlans [gs] (map snd applicable') (map (\m -> (m, arepr m)) moves) (alpha opts) (iterations opts)
                                makeresult (actions,qual,goal) = mytrace Agents ("got quality: " ++ (show qual) ++ " for " ++ (show goal)) (map fst actions,goal,qual,gen)
                                best_plan = makeresult $ maximumBy (comparing snd3) plans'

intentionalMove :: PlanningDomain a b c d x => String -> a -> [([(d,Term d)],c,c)] -> Commitment -> [b] -> Context -> MOptions -> State (c,[b],Quality,StdGen) b
intentionalMove name gs strat Fanatical moves ctx opts = do
                                               (intention, plan, qual,gen) <- get
                                               if null plan then do
                                                   let (newplan,newgoal,newqual,newgen) = bestIntention name gs strat moves ctx gen opts
                                                   if null newplan then return $ head moves
                                                   else do
                                                      put (newgoal, mytrace Agents ("\n!!!Plan (" ++ name ++ "): "++ (intercalate "\n" $ map show $ newplan) ++ "\n goal: " ++ (take 20 $ show newgoal)) $ tail newplan, newqual, newgen)
                                                      return $ head newplan
                                               else do
                                                   let next = head plan
                                                   put (intention, mytrace Agents ("\n!!!Old Plan (" ++ name ++ "): " ++ (show $ length plan)) $ tail plan, qual, gen)
                                                   return next
intentionalMove name gs strat Capricious moves ctx opts = do  
                                               (_, _, _, gen) <- get                                             
                                               let (newplan,newgoal,newqual,newgen) = bestIntention name gs strat moves ctx gen opts
                                               if null newplan then return $ head moves
                                               else do
                                                  put (newgoal, tail newplan, newqual, gen)
                                                  return $ head newplan
intentionalMove name gs strat (Balanced al) moves ctx opts = do
                                               (intention, plan,qual,gen) <- get
                                               let (newplan,newgoal,newqual,newgen) = bestIntention name gs strat moves ctx gen opts
                                               if (null plan) || (reconsider gs plan newplan qual newqual al) then do
                                                   if null newplan then return $ head moves
                                                   else do
                                                      put (newgoal, tail newplan, newqual, newgen)
                                                      return $ head newplan
                                               else do
                                                   let next = head plan
                                                   put (intention,tail plan, qual, gen)
                                                   return next
                                                   
resetIAgent :: PlanningDomain a b c d x => State (c,[b],Quality,StdGen) Int
resetIAgent = do
                (_,_,_,gen) <- get
                put (defaultgoal, [], (False,zero), gen)
                return 0
        
getGen :: RandomAgent -> StdGen
getGen (RA g) = g

resetPlayer :: PlanningDomain a b c d x => Agent c b d -> Agent c b d
resetPlayer (IAgent (IA strat state comm) name ctx) = IAgent (IA strat newstate comm) name ctx
                           where
                            (_,newstate) = runState (resetIAgent) state
resetPlayer p = p

turn :: PlanningDomain a b c d x => Agent c b d -> a -> [b] -> MOptions -> IO (b, Agent c b d)
turn (RAgent rando name) _ moves _ = return (m,RAgent (RA a) name)
                            where
                             (m,a) = runRand (randomMove moves) $ getGen rando
turn (CAgent cnt name) _ moves _ = return (m,CAgent (CA newcnt) name)
                            where
                              (m,newcnt) = countingMove cnt moves
turn (NAgent name) _ moves _ = return (head moves, NAgent name)
turn (IOAgent name) _ moves _ = do
                                  foldl1 (>>) [putStrLn $ arepr m | m <- moves]
                                  putStrLn $ "Choose one of " ++ (show $ length moves) ++ " actions"
                                  which <- getLine
                                  let i = read which :: Int
                                  return (moves!!i, IOAgent name)
turn (IAgent (IA strat state comm) name ctx) gstate moves opts = return (m, IAgent (IA strat newstate comm) name ctx)
                           where
                            (m,newstate) = runState (intentionalMove name gstate strat comm moves ctx opts) state


            
