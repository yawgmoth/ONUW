module BaltagExecution where

import Baltag
import BaseTypes
import Debug.Trace
import qualified Data.Map as Map
import qualified Data.Set as Set

data FullAction = FA (Action Int) (Proposition Int) (Set.Set (AtProp Int)) (Map.Map String [FullAction]) String deriving (Show,Read,Eq)

faRep (FA action pres cont alts output) = show action

toFullAction actors action = FA action (pre action) (content action) (Map.fromList [(a,map (toFullAction actors) $ alternatives a action) | a <- actors]) (output action)
toFullActions actors action = [FA act (pre act) (content act) (Map.fromList [(a,map (toFullAction actors) $ alternatives a act) | a <- actors]) (output act)  | act <- choice action]




execute :: PointedModel -> Action Int -> [(PointedModel,String)]
execute state act = cleanup [executeSimple state a | a <- choice act]

{-executeTrace :: PointedModel -> [Action Int] -> [(PointedModel,String)]
executeTrace state [] = [(state,"")]
executeTrace start (act:acts) = foldl (++) [] [executeTrace s' acts | s' <- executeActions start $ choice act] -}

executeActions :: PointedModel -> [Action Int] -> [(PointedModel,String)]
executeActions s acts = cleanup [executeSimple s a | a <- acts]

executeAll :: [PointedModel] -> [Action Int] -> [(PointedModel,String)]
executeAll [] _ = []
executeAll (x:xs) a = news ++ (executeAll xs a)
                    where
                        news = cleanup [executeSimple x a' | a' <- a]

executeSimple :: PointedModel -> Action Int -> Maybe (PointedModel,String)
{-executeSimple s@(PM app fact actors) a | canExecute s a = Just $ PM (\act -> Map.findWithDefault (looksLike act) act appearanceMap) (fact `symdiff` (content a)) actors
                                       | otherwise      = Nothing
                                                         where
                                                            looksLike act = cleanup [executeSimple s' a' | s' <- app act, a' <- alternatives act a]
                                                            appearanceMap = Map.fromList [(actor,looksLike actor) | actor <- actors] -}


executeSimple s@(PM app fact actors _ _) act = executeFull s $ toFullAction actors act 
                                                         
executeFull :: PointedModel -> FullAction -> Maybe (PointedModel,String)
executeFull s@(PM app fact actors ctx props) (FA action pres cont alts output) | interprets s pres = Just $ (PM appearanceMap (fact `symdiff` cont) actors ctx newprops, output)
                                                                               | otherwise      = Nothing
                                                         where
                                                            looksLike act = map fst $ cleanup [executeFull s' a' | s' <- Map.findWithDefault [] act app, a' <- Map.findWithDefault [fullSkip] act alts]
                                                            appearanceMap = Map.fromList [(actor,looksLike actor) | actor <- actors] 
                                                            fullSkip = toFullAction actors skip
                                                            newprops = props -- todo

canExecute :: PointedModel -> Action Int -> Bool
canExecute s a = interprets s $ pre a

interprets :: PointedModel -> Proposition Int -> Bool
interprets pm p = result -- trace (">>>> " ++ (show p) ++ " in " ++ (show $ fact pm) ++ " -> " ++ (show result) ++ "\n") result
               where 
                  result = interprets' pm p

interprets' :: PointedModel -> Proposition Int -> Bool
interprets' s@(PM app fact _ _ _) (Atom (Predicate 0 [])) = True
interprets' s@(PM app fact _ _ _) (Atom a) = inatom s (Atom a)
interprets' s@(PM app fact _ _ _) (Not p) = innot s (Not p)
interprets' s@(PM app fact _ _ _) (Or p1 p2) = inor s (Or p1 p2)
interprets' s@(PM app fact _ _ _) (And p1 p2) = inand s (And p1 p2)
interprets' s@(PM app fact _ _ _) (Know act p) = inknows s (Know act p) 
interprets' s@(PM app fact _ _ _) (StrongKnow act p) = (not $ null poss) && (and [interprets s' p | s' <- poss])
                                                     where
                                                        poss = Map.findWithDefault [] act app
interprets' s@(PM app fact _ _ _) (ProbablyKnow op prob act p) = (not $ null poss) && (cmpprob op prob actualprob)
                                                              where
                                                                  poss = Map.findWithDefault [] act app
                                                                  holds = length $ filter (\s' -> interprets s' p) poss
                                                                  count = length poss
                                                                  actualprob = (fromIntegral holds) / (fromIntegral count)
interprets' s@(PM app fact _ _ _) (Apply act p) = inapply s (Apply act p)
interprets' s@(PM app fact _ ctx _) (PropertyEquality a b) = (propertyValueB fact ctx a) == (propertyValueB fact ctx b)
interprets' _ _ = False
--interprets s@(PM app fact) (MutualKnowledge acts p) = and [interprets s' p | s' <- app act]
                             
               
inknows s@(PM app fact _  _ _) (Know act p) = (and [interprets s' p | s' <- poss])
                                       where
                                           poss = Map.findWithDefault [] act app
inatom s@(PM app fact _ _ _) (Atom a) = a `Set.member` fact
innot s@(PM app fact _ _ _) (Not p) = not $ interprets s p
inor s@(PM app fact _ _ _) (Or p1 p2) = (interprets s p1) || (interprets s p2)
inand s@(PM app fact _ _ _) (And p1 p2) = (interprets s p1) && (interprets s p2)
inapply s@(PM app fact _ _ _) (Apply act p) = and [interprets s' p | (s',o) <- execute s act]
               



