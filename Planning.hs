{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE UndecidableInstances #-}
module Planning where


import qualified Data.Map as Map
import Baltag
import BaltagExecution
import AbstractActions
import AbstractActionExecution
import BaseTypes
import Debug.Trace
import Control.Parallel.Strategies
import Data.List
import ActionCompiler
import Data.Ord
import qualified Data.Set as Set
import qualified Data.Array.IArray as Array
import qualified Data.Array.Unboxed as UArray

suspectlist alist ctx = foldl (++) [] [map (\act -> (Learn action act, act ++ " suspects " ++ aname)) $ actors ctx | (action,aname) <- alist]

makeActionList 0 al ctx = al
makeActionList n al ctx =  (makeActionList (n-1) al ctx) ++ (suspectlist al ctx)

makeFinalState :: (a,[(b,String)]) -> (a,[String])
makeFinalState (s,t) = (s,map snd t)

makeActions :: PlanningDomain a b c d x => ((a,String),[(b,String)]) -> [b]
makeActions (s,t) = map fst t

calculatePotentialPlans ::  PlanningDomain a b c d x => [a] -> [c] -> [(b,String)] -> Float -> Int -> [([(b,String)],Quality,c)]
calculatePotentialPlans states goals actions alpha maxn = multiSearch initstates goals actions alpha maxn 0
                                            where
                                               initstates = map (\a -> (a,[],0,(False,0),head goals)) states


type Quality = (Bool, Float)

nscore alpha ((a,b),p) = (a,(-b/(one + alpha * log (one + (fromIntegral $ length p)))))
 
calculateQuality :: PlanningDomain a b c d x => (a,[(b,String)],Int,Quality,c) -> [c] -> (a,[(b,String)],Int,Quality,c)
calculateQuality (state, plan, minaction,_,_) goals = (state,plan,minaction,q,g)
                                                where
                                                   (q,g) = maximumBy (comparing fst) goalqualities
                                                   goalqualities = map (\g -> (quality state g, g)) goals

calculateNextQuality' :: PlanningDomain a b c d x => (a,[(b,String)],Int,Quality,c) -> (b,String) -> Int -> [c] -> [(a,[(b,String)],Int, Quality,c)] 
calculateNextQuality' (state,plan,minaction,qual,goal) (act,name) ind goals = [calculateQuality (newstate,plan ++ [(act,name)], ind, qual, goal) goals | newstate <- map fst $ executeAction state act]

calculateNextQuality ::  PlanningDomain a b c d x => (a,[(b,String)],Int, Quality,c) -> [(b,String)] -> [c] -> ([(a,[(b,String)],Int, Quality,c)],Int)
calculateNextQuality (state,plan,minaction,qual,goal) actions goals = (concat $ map (\(a,i) -> calculateNextQuality' (state,plan,minaction,qual,goal) a (i+minaction) goals) $ zip actions [0..], length eligible)
                                         where
                                            eligible = drop minaction actions
                                         

multiSearch :: PlanningDomain a b c d x => [(a,[(b,String)], Int, Quality, c)] -> [c] -> [(b,String)] -> Float -> Int -> Int -> [([(b,String)],Quality,c)]
multiSearch frontier goals actions alpha maxeval curreval = if unsolvable then (nubBy cmpGoals $ sortBy cmpScores $ extractPlans frontier) else 
                                                if null solvedstates then multiSearch newfrontier goals actions alpha maxeval (curreval + evals) else solvedstates
                                             where
                                                extractPlans = map (\(_,p,_,s,g) -> (p,s,g)) 
                                                cmpScores (p1,s1,_) (p2,s2,_) = comparing (nscore alpha) (s1,p1) (s2,p2)
                                                cmpScores5 (_,p1,_,s1,_) (_,p2,_,s2,_) = comparing (nscore alpha) (s1,p1) (s2,p2)
                                                cmpGoals (_,_,c1) (_,_,c2) = c1 == c2
                                                unsolvable = (curreval >= maxeval)
                                                frontier' = sortBy cmpScores5 frontier
                                                nextState = head frontier'
                                                (newState,evals) = calculateNextQuality nextState actions goals
                                                solvedstates = map (\(s,p,_,(done,q),g) -> (p,(done,q),g)) $ filter (\(_,_,_,(done,_),_) -> done) frontier
                                                
                                                newfrontier = newState ++ (tail frontier')
                                        

calculatePlan ::  PlanningDomain a b c d x => [a] -> c -> [b] -> [b]
calculatePlan states goal actionlist = if null steps then [] else makeActions $ head steps
                                   where
                                       steps = heuristicSearch (map (\s -> ((s,""),[])) states) goal (map (\a -> (a,"")) actionlist) (-1)
                                       
calculateLimitedPlan ::  PlanningDomain a b c d x => [a] -> c -> [b] -> Int -> [b]
calculateLimitedPlan states goal actionlist maxlen = if null steps then [] else makeActions $ head steps
                                   where
                                      steps = heuristicSearch (map (\s -> ((s,""),[])) states) goal (map (\a -> (a,"")) actionlist) maxlen

makeActionSequences :: [b] -> Int -> [[b]]
makeActionSequences _ 0 = []
makeActionSequences actions 1 = [[a] | a <- actions]
makeActionSequences actions n = (makeActionSequences actions (n-1)) ++ [a:s | a <- actions, s <- makeActionSequences actions (n-1)]
                       
bruteforce :: PlanningDomain a b c d x => [a] -> c -> [b] -> Int -> [b]
bruteforce states goal actions maxlen = trace ("found a plan with length " ++ (show $ length result)) result
                                   where 
                                      actionseqs' = makeActionSequences actions maxlen
                                      actionseqs = trace ("have sequences: " ++ (show $ length actionseqs') ++ " with max len " ++ (show maxlen)) actionseqs'
                                      result = bruteforce' (head states) goal actionseqs
                       

bruteforce' :: PlanningDomain a b c d x => a -> c -> [[b]] -> [b]
bruteforce' state goal [] = []
bruteforce' state goal (x:xs) = if reached `interpretsCondition` goal then x else bruteforce' state goal xs
                             where
                                reached = chainExecute state x

chainExecute :: PlanningDomain a b c d x => a -> [b] -> a
chainExecute state [] = state
chainExecute state (x:xs) = if null next then state else chainExecute (fst $ head $ next) xs
                         where
                            next = executeAction state x

planBaltag :: [PointedModel] -> Action Int -> Map.Map String (AbstractAction String) -> Context -> Map.Map Int String -> Int -> [((PointedModel,String),[String])]
-- plan states = bfsplan' (map (\s -> ((s,""),[])) states) 
planBaltag states goal actionmap ctx ids suspicionlevels = plan states goal (toActionList actionmap ctx suspicionlevels)
                                                     
plan :: PlanningDomain a b c d x => [a] -> c -> [(b,String)] -> [((a,String),[String])]
plan states goal actions = map makeFinalState $ heuristicSearch (map (\s -> ((s,""),[])) states) goal actions (-1)

planLimited :: PlanningDomain a b c d x => [a] -> c -> [(b,String)] -> Int -> [((a,String),[String])]
planLimited states goal actions maxlen = map makeFinalState $ heuristicSearch (map (\s -> ((s,""),[])) states) goal actions maxlen




toActionList :: Map.Map String (AbstractAction String) -> Context -> Int -> [(Action Int,String)]
toActionList actionmap ctx suspicionlevels = makeActionList suspicionlevels actionlist ctx
                                           where
                                              actionlist = concat [argAssignments action ctx name | (name,action) <- Map.toList actionmap]

argAssignments action ctx aname = [(compile action ctx $ Map.fromList $ zip argnames args, aname ++ "(" ++ (intercalate ", " $ map (toStringValue ctx) args) ++ ")") | args <- sequence [getSet ctx arg | arg <- getArgTypes action] ]
                          where
                              argnames = getArgNames action  

addSuspect :: AbstractActionType a => [(AbstractAction a,String)] -> Context -> [(AbstractAction a, String)]
addSuspect alist ctx = concat [map (\act -> (SuspectAction (fromStringValue ctx act) action, act ++ " suspects " ++ aname)) $ actors ctx | (action,aname) <- alist]

actionList :: AbstractActionType a => Int -> [(AbstractAction a,String)] -> Context -> [(AbstractAction a,String)]
actionList 0 al ctx = al
actionList n al ctx = (actionList (n-1) al ctx) ++ (addSuspect al ctx)

groundAction :: AbstractActionType a => AbstractAction a -> Context -> String -> [(AbstractAction a,String)]
groundAction action ctx aname = [(resolveArgs ctx (Map.fromList $ zip argnames args) action $ call aname args, call aname args) | args <- sequence [getSet ctx arg | arg <- argtypes] ]
                          where
                              argnames = getArgNames action
                              argtypes = getArgTypes action
                              strargs args = map (toStringValue ctx) args
                              call aname args = formatCall aname $ strargs args

generateOptions :: AbstractActionType a => Context -> Map.Map String (AbstractAction a) -> [(AbstractAction a,String)]
generateOptions ctx actions = concat $ map (\(aname,action) -> groundAction action ctx aname) $ Map.toList actions

groundAgentAction action ctx aname agent = [(resolveArgs ctx (Map.fromList $ zip argnames (agent:args)) action $ call aname args, call aname args) | args <- sequence [getSet ctx arg | arg <- argtypes] ]
                          where
                              argnames = getArgNames action
                              argtypes = tail $ getArgTypes action
                              strargs args = map (toStringValue ctx) (agent:args)
                              call aname args = formatCall aname $ strargs args

generateAgentOptions :: AbstractActionType a => Context -> Map.Map String (AbstractAction a) -> a -> [(AbstractAction a,String)]
generateAgentOptions ctx actions agent = concat $ map (\(aname,action) -> groundAgentAction action ctx aname agent) $ Map.toList actions
  
type State = (PointedModel,String)
type Trace = [(Action Int,String)]

shortenough _ (-1) = True
shortenough t n = (length t) < n

applyActions :: PlanningDomain a b c d x => [((a,String),[(b,String)],Int)] -> [(b, Int, String)] -> Int -> [((a,String),[(b,String)],Int,[(Int,Int)])]
applyActions frontier actions maxlen = filter (\(_,t,_,acts) -> (not $ null acts) && (shortenough t maxlen)) $ map (applyAction actions) frontier

applyAction :: PlanningDomain a b c d x => [(b, Int, String)] -> ((a,String),[(b, String)],Int) -> ((a,String),[(b,String)],Int,[(Int,Int)])
applyAction actions (s,t,c) = (s,t,c,applyAction' actions 0 (s,t,c))

applyAction' :: PlanningDomain a b c d x => [(b, Int, String)] -> Int -> ((a,String),[(b,String)],Int) -> [(Int,Int)]
applyAction' [] _ _ = []
applyAction' ((x,xc,name):xs) n ((m,o),t,c) = if applicable m x then (n,xc):(applyAction' xs (n+1) ((m,o),t,c)) else applyAction' xs (n+1) ((m,o),t,c)

findMin :: [(a,b,Int,[(Int,Int)])] -> (Maybe (a,b,Int,[(Int,Int)]),Int)
findMin frontier = (s,si)
                where
                   (s,c,si) = findMin' frontier 0

findMin' :: [(a,b,Int,[(Int,Int)])] -> Int -> (Maybe (a,b,Int,[(Int,Int)]),Int,Int)
findMin' [] _ = (Nothing,-1,-1)
findMin' ((s,t,c,actions):xs) n = better (Just (s,t,c,actions),bestcost,n) $ findMin' xs (n+1)
                               where
                                   better (s1,cost1,i1) (s2,cost2,i2) = if (cost2 < 0) || (cost1 < cost2) then (s1,cost1,i1) else (s2,cost2,i2)
                                   bestcost = c + ac
                                   (ai,ac) = head actions
                                   
foundState Nothing = False
foundState (Just s) = True

extractState (Just s) = s

calculateHeuristic :: [(Action Int,String)] -> [Action Int] -> [(Action Int,Int,String)]
calculateHeuristic [] _ = []
calculateHeuristic _ [] = []
calculateHeuristic actions goals = if Set.null goalTerms then [] else matching ++ nextlevel
                                where
                                   (a,b) = partition matchGoals actions
                                   (a1,b1) = partition matchB actions
                                   matching =  (map (\(a,r) -> (a,2,r)) a1) ++ (map (\(a,r) -> (a,1,r)) a)
                                   nextlevel = map (\(a,c,n) -> (a,c+2,n)) $ calculateHeuristic b $ map fst a
                                   goalTerms = foldl (Set.union) Set.empty $ map getPreTerms goals
                                   toB s = Set.filter (\s -> s /= "") $ Set.map (\(act,_) -> act) s
                                   goalB = toB goalTerms -- trace (name ++ "\n" ++ (show goalTerms) ++ " vs " ++ (show $ getFlipTerms action) ++ "\n")
                                   matchGoals (action,name) =   not $ Set.null $ Set.intersection goalTerms $ getFlipTerms action
                                   matchB (action,name) =   not $ Set.null $ Set.intersection goalB $ toB $ getFlipTerms action

--trace ("B: " ++ name ++ "\n" ++ (show goalB) ++ " vs " ++ (show $ toB $ getFlipTerms action) ++ "\n")
getFlipTerms :: Action Int -> Set.Set (String,Int)
getFlipTerms (Flip (Predicate a _)) = Set.singleton ("",a)
getFlipTerms (Choice a b) = Set.union (getFlipTerms a) $ getFlipTerms b
getFlipTerms (Composition a b) = Set.union (getFlipTerms a) $ getFlipTerms b
getFlipTerms (MutualLearn act acts) = Set.unions [Set.union (learn a) $ Set.map (\(b,p) -> (a++b,p)) $ getPreTerms act | a <- acts]
                                 where 
                                      sub = getFlipTerms act
                                      learn a = Set.union sub $ Set.map (\(b,p) -> (a++b,p)) $ sub
getFlipTerms (Learn act a) = Set.union learn $ Set.map (\(b,p) -> (a++b,p)) $ getPreTerms act
                           where
                              sub = getFlipTerms act
                              learn = Set.map (\(b,p) -> (a++b,p)) $ sub
getFlipTerms _ = Set.empty
                                   
getPreTerms :: Ord a => Action a -> Set.Set (String,a)
getPreTerms (Test prop) = getPropTerms prop
getPreTerms (Choice a b) = Set.union (getPreTerms a) $ getPreTerms b
getPreTerms (Composition a b) = Set.union (getPreTerms a) $ getPreTerms b
getPreTerms (MutualLearn act _) = getPreTerms act
getPreTerms (Learn act a) = Set.empty
getPreTerms _ = Set.empty

getPropTerms (Atom (Predicate a _)) = Set.singleton ("",a)
getPropTerms (Not prop) = getPropTerms prop
getPropTerms (Or a b) = Set.union (getPropTerms a) $ getPropTerms b
getPropTerms (And a b) = Set.union (getPropTerms a) $ getPropTerms b
getPropTerms (Apply a b) = Set.union (getPreTerms a) $ getPropTerms b
getPropTerms (Know a x) = Set.map (\(b,p) -> (a++b,p)) $ getPropTerms x
getPropTerms (StrongKnow a x) = Set.map (\(b,p) -> (a++b,p)) $ getPropTerms x
getPropTerms (ProbablyKnow _ _ a x) = Set.map (\(b,p) -> (a++b,p)) $ getPropTerms x
getPropTerms (MutualKnowledge acts x) = Set.unions [Set.map (\(b,p) -> (a++b,p)) $ getPropTerms x | a <- acts]
getPropTerms (PropertyEquality a b) = Set.union (propertyName a) $ propertyName b
getPropTerms (PropertyInequality a b) = Set.union (propertyName a) $ propertyName b

propertyName (BaltagPropertyN a _) = Set.singleton ("",a)
propertyName (Value a) = Set.empty

ostariHeuristic :: AbstractActionType a => [(AbstractAction a, String)] -> [Predicate a] -> [(AbstractAction a,Int,String)]
ostariHeuristic actions goal = trace ((show goal) ++ (show $ map getReferences goal)) $ ostariHeuristic' actions $ Set.unions $ map getReferences goal

ostariHeuristic' :: AbstractActionType a => [(AbstractAction a, String)] -> Set.Set (BeliefLayers a,a) -> [(AbstractAction a,Int,String)]
ostariHeuristic' [] _ = []
ostariHeuristic' actions goals
                     | Set.null goals = []
                     | otherwise = matching ++ nextlevel ++ nextlevel1
                                where
                                   (a,b) = partition matchGoals actions
                                   (a1,b1) = partition matchB actions
                                   matching =  (map (\(a,r) -> (a,2,r)) a1) ++ (map (\(a,r) -> (a,1,r)) a)
                                   nextlevel = map (\(a,c,n) -> (a,c+2,n)) $ ostariHeuristic' b $ Set.unions $ map (getRequirements . fst) a
                                   nextlevel1 = map (\(a,c,n) -> (a,c+3,n)) $ ostariHeuristic' b1 $ Set.unions $ map (getRequirements . fst) a1
                                   toB s = Set.filter (not . emptyBL) $ Set.map (fst) s
                                   goalB = toB goals
                                   matchGoals (action,name) = not $ Set.null $ Set.intersection goals $ getChanges action
                                   matchB (action,name) = not $ Set.null $ Set.intersection goalB $ toB $ getChanges action


class (Show b, Eq b, Eq c, Show c, AbstractActionType d, GenArray d x) => PlanningDomain a b c d x | a -> b, a -> c, b -> a, b -> c, c -> a, c -> b, a -> d, b -> d, c -> d, a -> x, b -> x, c -> x where
    interpretsCondition :: a -> c -> Bool
    quality :: a -> c -> (Bool,Float)
    quality pm c = if interpretsCondition pm c then (True,1) else (False,0)
    applicable :: a -> b -> Bool
    executeAction :: a -> b -> [(a,String)]
    heuristic :: [(b,String)] -> [c] -> [(b,Int,String)]
    assignArgs :: AbstractAction d -> Context -> Map.Map d d -> String -> b
    assignArgsPredicate :: Predicate d -> Context -> Map.Map d d -> c
    defaultgoal :: c    
    propertyValue :: Context -> a -> d -> [d] -> String
    getTermValue :: Context -> a -> Term d -> d
    getTermValue ctx pm t = fromStringValue ctx $ propertyValue ctx pm (termName t) $ map (getTermValue ctx pm) $ termArgs t
    getBindingValue :: Context -> a -> Term d -> Int -> d
    getBindingValue ctx pm t _ = fromStringValue ctx $ propertyValue ctx pm (termName t) $ map (getTermValue ctx pm) $ termArgs t -- TODO: support random in all cases
    assignStringArgToPredicate :: Context -> Predicate d -> String -> String -> c
    assignArgsExtra :: AbstractAction d -> Context -> d -> String -> Map.Map d d -> String -> b
    resolveBindingsP :: Context -> c -> Map.Map d d -> c
    arepr :: b -> String
    arepr = show
    toDebug :: a -> Context -> d -> String
    toDebug _ _ = show
    
instance PlanningDomain PointedModel (Action Int) (Action Int) String Array.Array where
    interpretsCondition = canExecute
    applicable = canExecute
    executeAction = execute
    heuristic = calculateHeuristic
    assignArgs a ctx m _ = compile a ctx m
    assignArgsExtra action ctx name value argmap aname = compile action ctx $ Map.insert name value argmap
    assignArgsPredicate a ctx argmap = compilePredicate (resolveVarsPredicate argmap a) ctx
    defaultgoal = testtrue
    propertyValue = getValue 
    assignStringArgToPredicate ctx a name value = assignArgsPredicate a ctx (Map.singleton name value)
    resolveBindingsP ctx act varmap = resolveVars (convertVarMap varmap $ ids ctx) act
    
    
{- instance (AbstractActionType a, GenArray a x) => PlanningDomain (PointedModelA a (x (Int,Int) a)) (AbstractAction a) (Predicate a) a x where
    interpretsCondition = interpretsA
    applicable = canExecuteA
    executeAction = executeA
    heuristic = ostariHeuristic
    assignArgs action ctx args = resolveArgs ctx args action
    assignArgsExtra action ctx name value argmap = resolveArgs ctx (Map.insert name (fromStringValue ctx value) argmap) action 
    assignArgsPredicate a ctx argmap = resolveVarsPredicate argmap a
    defaultgoal = tautology
    propertyValue ctx pm prop args = toStringValue ctx (if prop `elem` (getIndices ctx) then termValue pm query else termValue pm (PropertyN prop $ map Constant args))
                 where 
                     query = (IndexedProperty (toIndex ctx prop) $ Constant $ head args)
    assignStringArgToPredicate ctx a name value = assignArgsPredicate a ctx (Map.singleton (fromStringValue ctx name) $ fromStringValue ctx value) -}
   
instance PlanningDomain (PointedModelA String SArray) (AbstractAction String) (Predicate String) String Array.Array where
    interpretsCondition = interpretsA
    quality = qualityA
    applicable = canExecuteA
    executeAction = executeA
    heuristic = ostariHeuristic
    assignArgs action ctx args = resolveArgs ctx args action
    assignArgsExtra action ctx name value argmap = resolveArgs ctx (Map.insert name value argmap) action 
    assignArgsPredicate a ctx argmap = resolveVarsPredicate argmap a
    defaultgoal = tautology
    propertyValue ctx pm prop args = (if prop `elem` (getIndices ctx) then termValue pm query else termValue pm (PropertyN prop $ map Constant args))
                 where 
                     query = (IndexedProperty (toIndex ctx prop) $ Constant $ head args)
    getTermValue ctx = termValue
    getBindingValue = getBValueA
    assignStringArgToPredicate ctx a name value = assignArgsPredicate a ctx (Map.singleton (fromStringValue ctx name) value)
    resolveBindingsP ctx act varmap = resolveVarsPredicate varmap act
    arepr = pvname
   
instance PlanningDomain (PointedModelA Int IArray) (AbstractAction Int) (Predicate Int) Int UArray.UArray where
    interpretsCondition = interpretsA
    quality = qualityA
    applicable = canExecuteA
    executeAction = executeA
    heuristic = ostariHeuristic
    assignArgs action ctx args = resolveArgs ctx args action
    assignArgsExtra action ctx name value argmap = resolveArgs ctx (Map.insert name (fromStringValue ctx value) argmap) action 
    assignArgsPredicate a ctx argmap = resolveVarsPredicate argmap a
    defaultgoal = tautology
    propertyValue ctx pm prop args = toStringValue ctx (if prop `elem` (getIndices ctx) then termValue pm query else termValue pm (PropertyN prop $ map Constant args))
                 where 
                     query = (IndexedProperty (toIndex ctx prop) $ Constant $ head args)
    getTermValue ctx = termValue
    getBindingValue = getBValueA
    assignStringArgToPredicate ctx a name value = assignArgsPredicate a ctx (Map.singleton (fromStringValue ctx name) $ fromStringValue ctx value)
    resolveBindingsP ctx act varmap = resolveVarsPredicate varmap act
    arepr = pvname
    toDebug _ ctx x = intToStr ctx x

heuristicSearch :: PlanningDomain a b c d x => [((a,String),[(b,String)])] -> c -> [(b,String)] -> Int -> [((a,String),[(b,String)])]
heuristicSearch states goal actionmap maxlen = if or $ map (\((s,o),t) -> interpretsCondition s goal) states then states else sub $ applyActions states' actions maxlen
                                       where
                                           actions' = heuristic actionmap [goal]
                                           actions = mytrace Planning ("actions: " ++ (intercalate "\n" $ map (\(a,v,n) -> (arepr a) ++ ": " ++ (show v)) actions')) actions'
                                           states' = map (\(s,t) -> (s,t,0)) states
                                           sub x = heuristicSearch' x goal actions maxlen


formatF :: ((a,String),[(b,String)],Int,[(Int,Int)]) -> String
formatF (a,b,c,d) = "node (" ++ (show c) ++ ") : " ++ (intercalate ", " $ map (snd) $ b) ++ " -> " ++ (show d)

showF :: [((a,String),[(b,String)],Int,[(Int,Int)])] -> String
showF frontier = "Frontier: \n  " ++ (intercalate "\n  " $ map (formatF) frontier)
                                                                   
heuristicSearch' :: PlanningDomain a b c d x => [((a,String),[(b,String)],Int,[(Int,Int)])] -> c -> [(b,Int,String)] -> Int -> [((a,String),[(b,String)])]
heuristicSearch' frontier goal actions maxlen = if unsolvable then [] else 
                                                if null solvedstates then heuristicSearch' newfrontier goal actions maxlen else solvedstates
                                             where
                                                (expandstate,i) = findMin frontier
                                                aname (a,b,c) = c
                                                ((m,o),t,c,a) = extractState expandstate
                                                unsolvable = (not $ foundState expandstate) || null a
                                                (action,cost,name) = actions!! (fst $ head a)
                                                newstates = map (\(m1,o1) -> ((m1,o++o1),t ++ [(action, name)],c+cost)) $ executeAction m action
                                                solvedstates = map (\(s,t,c1) -> (s,t)) $ filter (\((m,o),t,c1) -> interpretsCondition m goal) newstates
                                                newf1 = ((m,o),t,c,tail a)
                                                newf2 = applyActions newstates actions maxlen
                                                insertfrontier = if null $ tail a then newf2 else newf1:newf2
                                                frontierpre = take i frontier
                                                frontierpost =  drop (i+1) frontier
                                                newfrontier = frontierpre ++ insertfrontier ++ frontierpost


{-bfsplan' :: [(State,Trace)] -> Action Int -> Map.Map String AbstractAction -> Context -> Map.Map Int String -> Int -> [((PointedModel,String),Trace)]
bfsplan' states goal actionmap ctx ids suspicionlevels = bfsplan'' states goal allactions ctx ids
                          where
                              actionlist = foldl (++) [] [argAssignments action ctx name | (name,action) <- Map.toList actionmap]
                              
                              allactions = makeActionList suspicionlevels actionlist ctx
                              
bfsplan'' :: [(State,Trace)] -> Action Int -> [(Action Int,String)] -> Context -> Map.Map Int String -> [((PointedModel,String),Trace)]
bfsplan'' states goal allactions ctx ids = if null frontier then [] else if (or canexec) then map snd $ filter (fst) $ zip canexec states else bfsplan'' frontier goal allactions ctx ids
                          where
                              canexec = map (\((s,o),t) -> canExecute s goal) states 
                              frontier =  frontier'
                              frontier' = foldl (++) [] [map (\(s1,o1) -> ((s1,(o++o1)),t++[(compiled,repr)])) $ (execute s compiled `using` rpar) | ((s,o),t) <- states, (compiled,repr) <- allactions]

                              
                              
                              -}