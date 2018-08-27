{-# LANGUAGE BangPatterns #-}

module AbstractActionExecution where

import qualified Data.Map as Map
import Data.List
import BaseTypes
import AbstractActions
import Debug.Trace
import qualified Data.Array.Diff as Array

appearanceAMap pm = getAppearanceMap $ appearanceA pm
lockedAppearance pm = getLockedAppearance $ appearanceA pm

getWeightA (PMA { weightA = w }) = one / (one + w)


allActors (PMA {contextA =ctx})  = map (fromStringValue ctx) $ actors ctx

getAppearance (PMA {appearanceA = appearances} ) a = Map.findWithDefault [] a $ getAppearanceMap appearances



isIndexed :: (AbstractActionType a, GenArray a b) => PointedModelA a (b (Int,Int) a) -> Term a -> Bool
isIndexed (PMA {appearanceA=(App _ index), actorsA=actors}) item = False -- isFlat item && (Map.member name $ Map.findWithDefault Map.empty (head actors) index)
                                                 where
                                                     name = termName item
                                                     
isFlat (Property name arg) = isConstant arg
isFlat (Property2 name arg1 arg2) = isConstant arg1 && isConstant arg2
isFlat (PropertyN name args) = and (map (isConstant) args)
isFlat _ = False

isConstant (Constant _) = True
isConstant (Variable _) = True
isConstant _ = False

matchingWorlds :: (AbstractActionType a, GenArray a b) => PointedModelA a (b (Int,Int) a) -> a -> Term a -> a -> [PointedModelA a (b (Int,Int) a)]
matchingWorlds (PMA {appearanceA=(App _ index)}) actor left right = Map.findWithDefault [] (right:(map (termName) $ termArgs left)) $ Map.findWithDefault Map.empty (termName left) $ Map.findWithDefault Map.empty actor index

addWeight :: a -> PointedModelA a b -> (PointedModelA a b,Float)
addWeight w pm = (pm,one / (one + (weightA pm)))

interpretsA :: (AbstractActionType a, GenArray a b) => PointedModelA a (b (Int,Int) a) -> Predicate a -> Bool
interpretsA pm (Forall varname set condition) = all (\c -> interpretsA pm c) [resolveVarsPredicate (Map.singleton varname val) condition | val <- Map.findWithDefault [] set $ getSets $ contextA pm]
interpretsA pm (Exists varname set condition) = any (\c -> interpretsA pm c) [resolveVarsPredicate (Map.singleton varname val) condition | val <- Map.findWithDefault [] set $ getSets $ contextA pm]
interpretsA pm (Equal a b) = (termValue pm a) == (termValue pm b)
interpretsA pm (NotEqual a b) = (termValue pm a) /= (termValue pm b)
interpretsA pm (AndP a b) = (interpretsA pm a) && (interpretsA pm b)
interpretsA pm (OrP a b) = (interpretsA pm a) || (interpretsA pm b)
interpretsA pm (NotP a) = not $ interpretsA pm a
interpretsA pm (IsSet t) = (Map.member name $ staticsA pm) || (Map.member args $ Map.findWithDefault Map.empty name $ factsA pm)
                         where
                            name = termName t
                            args = [termValue pm arg | arg <- termArgs t]
interpretsA pm (IsUnSet t) = not $ interpretsA pm (IsSet t)
interpretsA pm (Believes actor condition) = (all (\w -> interpretsA w condition) app)
                                         where
                                             app = getAppearance pm actor
interpretsA pm (StrongBelieves actor condition) = (not $ null app) && (all (\w -> interpretsA w condition) app)
                                         where
                                             app = getAppearance pm actor
interpretsA pm (NotBelieves actor condition) = not $ all (\w -> interpretsA w condition) $ getAppearance pm actor
interpretsA pm (Probably op prob actor condition) = (not $ null app) && (cmpprob op prob actualprob)
                                         where
                                             app = getAppearance pm actor
                                             holds = length $ filter (\w -> interpretsA w condition) app
                                             count = length app
                                             actualprob = (fromIntegral holds) / (fromIntegral count)
interpretsA pm (WeightedProbably w op prob actor condition@(Equal a b)) | isConstant b && isIndexed pm a = trace ("using fast version") ((not $ null app) && (cmpprob op prob indexedprob))
                                                                        | otherwise                      = (not $ null app) && (cmpprob op prob actualprob)
                                         where
                                             app = getAppearance pm actor
                                             app' = map (addWeight w) app
                                             holds = (sum $ map snd $ filter (\(w,g) -> interpretsA w condition) app')
                                             count = (sum $ map snd app')
                                             actualprob =  holds / count
                                             indexedcount = (sum $ map getWeightA $ matchingWorlds pm actor a $ termName b)
                                             indexedprob = holds / indexedcount
                                             
interpretsA pm (WeightedProbably w op prob actor condition) = (not $ null app) && (cmpprob op prob actualprob)
                                         where
                                             app = getAppearance pm actor
                                             app' = map (addWeight w) app
                                             holds = (sum $ map snd $ filter (\(w,g) -> interpretsA w condition) app')
                                             count = (sum $ map snd app')
                                             actualprob =  holds / count
interpretsA pm (Each varname set condition) = True
interpretsA pm (Which varname set condition) = interpretsA pm (Exists varname set condition)

qualityA :: (AbstractActionType a, GenArray a b) => PointedModelA a (b (Int,Int) a) -> Predicate a -> (Bool, Float)
qualityA pm (Forall varname set condition) = (all fst sub, product $ map snd sub)
                                              where
                                                 sub = map (\c -> qualityA pm c) [resolveVarsPredicate (Map.singleton varname val) condition | val <- Map.findWithDefault [] set $ getSets $ contextA pm]
qualityA pm (Exists varname set condition) = (not $ null sub, val)
                                              where
                                                 quals = map (\c -> qualityA pm c) [resolveVarsPredicate (Map.singleton varname val) condition | val <- Map.findWithDefault [] set $ getSets $ contextA pm]
                                                 sub = filter (fst) $ quals
                                                 val = maximum $ map snd quals
qualityA pm (Equal a b) = if (termValue pm a) == (termValue pm b) then (True,1) else (False,0)
qualityA pm (NotEqual a b) = if (termValue pm a) /= (termValue pm b) then (True, 1) else (False, 0)
qualityA pm (AndP a b) = (at && bt, aq * bq)
                          where
                             (at,aq) = qualityA pm a
                             (bt,bq) = qualityA pm b
qualityA pm (OrP a b) = (at || bt, max aq  bq)
                          where
                             (at,aq) = qualityA pm a
                             (bt,bq) = qualityA pm b
qualityA pm (NotP a) = (not at, 1 - aq)
                        where
                           (at,aq) = qualityA pm a
qualityA pm (IsSet t) = if ((Map.member name $ staticsA pm) || (Map.member args $ Map.findWithDefault Map.empty name $ factsA pm)) then (True,1) else (False,0)
                         where
                            name = termName t
                            args = [termValue pm arg | arg <- termArgs t]
                            
qualityA pm (IsUnSet t) = (not at, 1 - aq)
                        where
                           (at,aq) = qualityA pm (IsSet t)
qualityA pm (Believes actor condition) = (all fst sub, product $ map snd sub)
                                         where
                                             app = getAppearance pm actor
                                             sub = map (\w -> qualityA w condition) app
qualityA pm (StrongBelieves actor condition) = if (not $ null app) then (all fst sub, product $ map snd sub) else (False,0)
                                         where
                                             app = getAppearance pm actor
                                             sub = map (\w -> qualityA w condition) app
qualityA pm (NotBelieves actor condition) = (not $ all fst sub, product $ map (\(t,q) -> 1-q) sub)
                                         where
                                             app = getAppearance pm actor
                                             sub = map (\w -> qualityA w condition) app
qualityA pm (Probably op prob actor condition) = if (not $ null app) then  (cmpprob op prob actualprob, actualprob) else (False,0)
                                         where
                                             app = getAppearance pm actor
                                             holds = length $ filter (\w -> interpretsA w condition) app
                                             count = length app
                                             actualprob = if count == 0 then 0 else (fromIntegral holds) / (fromIntegral count)
qualityA pm (WeightedProbably w op prob actor condition@(Equal a b)) | isConstant b && isIndexed pm a = if (not $ null app) then (cmpprob op prob indexedprob, indexedprob) else (False,0)
                                                                     | otherwise                      = if (not $ null app) then (cmpprob op prob actualprob, actualprob) else (False,0)
                                         where
                                             app = getAppearance pm actor
                                             app' = map (addWeight w) app
                                             holdsin = filter (\(w,g) -> interpretsA w condition) app' 
                                             holds = (sum $ map snd holdsin)
                                             count = (sum $ map snd app')
                                             actualprob = if count == 0 then 0 else holds / count
                                             indexedcount = (sum $ map getWeightA $ matchingWorlds pm actor a $ termName b)
                                             indexedprob = indexedcount / count --if indexedcount == 0 then 0 else holds / indexedcount
                                             
qualityA pm (WeightedProbably w op prob actor condition) = if (not $ null app) then (cmpprob op prob actualprob, actualprob) else (False, 0)
                                         where
                                             app = getAppearance pm actor
                                             app' = map (addWeight w) app
                                             holds = (sum $ map snd $ filter (\(w,g) -> interpretsA w condition) app')
                                             count = (sum $ map snd app')
                                             actualprob = if count == 0 then 0 else holds / count
                                             
qualityA pm (Each varname set condition) = (True,1)
qualityA pm (Which varname set condition) = qualityA pm (Exists varname set condition)

propName :: (AbstractActionType a, GenArray a b) => PointedModelA a (b (Int,Int) a) -> Term a -> [a]
propName pm (Property name arg) = [name, termValue pm arg]
propName pm (Property2 name arg1 arg2) = [name, termValue pm arg1, termValue pm arg2]
propName pm (PropertyN name args) = name:(map (termValue pm) args)
propName _ _ = []




resolveArgs :: AbstractActionType a => Context -> Map.Map a a -> AbstractAction a -> String -> AbstractAction a
resolveArgs ctx varmap action = resolveArgs' ctx varmap action []

resolveArgs' :: AbstractActionType a => Context -> Map.Map a a -> AbstractAction a -> [([a],a,a)] -> String -> AbstractAction a
resolveArgs' ctx varmap (PublicArgument varname setname action) args name = resolveArgs' ctx varmap action args name
resolveArgs' ctx varmap (SuspectAction actor action) args name = SuspectAction actor $ resolveArgs' ctx varmap action args name
resolveArgs' ctx varmap (SecretArgument actors varname setname action) args name = resolveArgs' ctx varmap action ((resolveList ctx varmap actors,varname,setname):args) name
resolveArgs' ctx varmap action [] name = PartiallyVisibleAction [] (resolveVarsAbstract ctx varmap action) [] name
--resolveArgs' ctx varmap action secretvars name = PartiallyVisibleAction actors (resolveVarsAbstract ctx varmap action) [resolveVarsAbstract ctx (updateMap varmap assignment) action | assignment <- assignments ] name
resolveArgs' ctx varmap action secretvars name = PartiallyVisibleAction actors (resolveVarsAbstract ctx varmap action) [resolveArgs' ctx (updateMap varmap assignment) action secretvars name | assignment <- assignments ] name
                                       where
                                           updateMap varmap assignment = Map.union (Map.fromList assignment) varmap
                                           assignments = sequence [[(v,val) | val <- getValues ctx set] | (actors,v,set) <- secretvars]
                                           actors = nub $ concat [a | (a,_,_) <- secretvars]
                                           
canExecuteA :: (AbstractActionType a, GenArray a b) => PointedModelA a (b (Int,Int) a) -> AbstractAction a -> Bool
canExecuteA pm (SuspectAction actor action) = all (\w -> canExecuteA w action) $ getAppearance pm actor
canExecuteA pm action = not $ null $ executeA pm action


executeA :: (AbstractActionType a, GenArray a b) => PointedModelA a (b (Int,Int) a) -> AbstractAction a -> [(PointedModelA a (b (Int,Int) a),String)]
executeA pm@(PMA {appearanceA=app, actorsA=acts}) (SuspectAction actor action) = [(pm {appearanceA=newappearance}, "")]
                                                                   where
                                                                      newappearance = makeAppWithRehash app [actor] (makeMap (appearance) acts)
                                                                      appearance a = if a == actor then concat [map fst $ executeA w action | w <- getAppearance pm a] else getAppearance pm a
                                                                      
executeA pm (PartiallyVisibleAction actors realaction [] _) = [(nw {appearanceA=appearance nw}, out) | (nw,out) <- newworlds]
                                                                   where
                                                                      newworlds = executeA' pm realaction
                                                                      applyAlternatives w a = concat [map fst $ executeA' w1 realaction | w1 <- getAppearance w a]
                                                                      appearance w = appearanceA w --makeMap (applyAlternatives w) $ actorsA pm
executeA pm action@(PartiallyVisibleAction actors realaction alternatives _) = [(nw {appearanceA=appearance nw}, out) | (nw,out) <- newworlds]
                                                                   where
                                                                      newworlds = executeA' pm realaction
                                                                      otheractors = (actorsA pm) \\ actors
                                                                      otheractor = if null otheractors then head actors else head otheractors
                                                                      dbg = "executeA: " ++ (show $ actors) ++ " -> " ++ (show $ length $ getAppearance pm otheractor) ++ "*" ++ (show $ length alternatives) ++ " and " ++ (show $ length $ getAppearance pm $ head actors)
                                                                      applyAlternatives w a = if a `elem` actors then concat [map fst $ executeA w1 action | w1 <- getAppearance w a] else concat [map fst $ executeA w1 a1 | w1 <- getAppearance pm a, a1 <- alternatives]
                                                                      
                                                                      -- Uses index, but also has to analyze the action
                                                                      -- if a `elem` actors then concat [map fst $ executeA w1 a1 | (a1,w1) <- restrictAppearance pm a action] else concat [map fst $ executeA' w1 a2 | a1 <- alternatives, (a2,w1) <- restrictAppearance pm a a1]
                                                                      appearance w = makeAppWithRehash (appearanceA w) (allActors pm) (makeMap (applyAlternatives w) $ actorsA pm) 
executeA pm a = executeA' pm a

prependOutput :: String -> (PointedModelA a b,String) -> (PointedModelA a b,String)
prependOutput s (pm,out) = (pm,s ++ out)

restrictAppearance :: (AbstractActionType a, GenArray a b) => PointedModelA a (b (Int,Int) a) -> a -> AbstractAction a -> [(AbstractAction a, PointedModelA a (b (Int,Int) a))]
restrictAppearance state actor action = matches
                                      where
                                          (restrictedaction,restriction) = restrictAction state action
                                          index = lockedAppearance state
                                          actormap = Map.findWithDefault Map.empty actor index
                                          isrestricted = Map.member actor index && (not $ null restriction) && (Map.member (head restriction) $ actormap)
                                          restrictionmap = Map.findWithDefault Map.empty (head restriction) actormap
                                          
                                          matches = if isrestricted then map (\w -> (restrictedaction,w)) $ Map.findWithDefault [] (tail restriction) restrictionmap
                                                                    else map (\w -> (action, w)) $ getAppearance state actor

isPrecondition (Precondition _) = True                                                                    
isPrecondition _ = False

reSequence :: AbstractActionType a => AbstractAction a -> AbstractAction a -> AbstractAction a
reSequence (Sequence x) (Sequence y) = Sequence (x++y)

addToSequence :: AbstractActionType a => AbstractAction a -> AbstractAction a -> AbstractAction a
addToSequence x (Sequence y) = Sequence (x:y)

restrictAction :: (AbstractActionType a, GenArray a b) => PointedModelA a (b (Int,Int) a) -> AbstractAction a -> (AbstractAction a, [a])
restrictAction pm (Sequence []) = (Sequence [], [])
restrictAction pm (Sequence ((Precondition (Equal a b)):xs)) | isConstant b && isIndexed pm a = (Sequence xs, trace ("using fast version for execution") [termName b, termName a] ++ (map (termName) $ termArgs a) )
                                                             | otherwise                      = (addToSequence (Precondition (Equal a b)) sub, restr)
                                                           where
                                                              (sub,restr) = restrictAction pm (Sequence xs) 
restrictAction pm (Sequence (x:xs)) = (addToSequence x sub,restr)
                                   where
                                       (sub,restr) = restrictAction pm (Sequence xs) 
                                     
restrictAction pm action = (action,[])

executeA' :: (AbstractActionType a, GenArray a b) =>  PointedModelA a (b (Int,Int) a) -> AbstractAction a -> [(PointedModelA a (b (Int,Int) a),String)]
executeA' pm (Sequence []) = [(pm,"")]
executeA' pm (Sequence (x:xs)) = concat $ map (\(m,s) -> map (prependOutput s) $ executeA' m (Sequence xs)) $ first
                               where
                                   first = executeA' pm x
executeA' pm (Inform actors (Each var set condition)) = [(pm {appearanceA=(makeAppWithRehash oldapp actors  (makeMap (appearance) (actorsA pm)))},"")]
                                                     where
                                                         appearance a = if a `elem` actors then [w | w <- Map.findWithDefault [] a appmap, w `interpretsA` conjunction] else Map.findWithDefault [] a appmap
                                                         conjunction = foldl1 (AndP) [chooseCondition $ resolveVarsPredicate (Map.singleton var val) condition | val <- values]
                                                         values = Map.findWithDefault [] set $ getSets $ contextA pm
                                                         chooseCondition c = if pm `interpretsA` c then c else NotP c
                                                         appmap = appearanceAMap pm
                                                         oldapp = appearanceA pm
executeA' pm (Inform actors (Which var set condition)) = [(pm {appearanceA=(makeAppWithRehash oldapp actors (makeMap (appearance c) (actorsA pm)))},"") | c <- conds]
                                                     where
                                                         appearance c a = if a `elem` actors then [w | w <- Map.findWithDefault [] a appmap, w `interpretsA` c] else Map.findWithDefault [] a appmap
                                                         conds = filter (interpretsA pm) [ resolveVarsPredicate (Map.singleton var val) condition | val <- values]
                                                         values = Map.findWithDefault [] set $ getSets $ contextA pm
                                                         appmap = appearanceAMap pm
                                                         oldapp = appearanceA pm
executeA' pm (Inform actors condition) = if (pm `interpretsA` condition) then [(pm {appearanceA=(App (makeMap (appearance) (actorsA pm)) $ lockedAppearance pm) },"")] else 
                                                                              [(pm {appearanceA=(App (makeMap (nappearance) (actorsA pm))  $ lockedAppearance pm)},"")]
                                       where
                                           appearance a = if a `elem` actors then [w | w <- Map.findWithDefault [] a appmap, w `interpretsA` condition] else Map.findWithDefault [] a appmap
                                           nappearance a = if a `elem` actors then [w | w <- Map.findWithDefault [] a appmap, not $ w `interpretsA` condition] else Map.findWithDefault [] a appmap
                                           appmap = appearanceAMap pm
executeA' pm (Suspect actors condition) = [(pm {appearanceA=(makeAppWithRehash (appearanceA pm) actors newapp)},"")]
                                       where
                                           appearance a = if a `elem` actors then [w | w <- Map.findWithDefault [] a appmap, w `interpretsA` condition] else Map.findWithDefault [] a appmap
                                           appmap = appearanceAMap pm
                                           newapp = makeMap (appearance) (actorsA pm)
executeA' pm@(PMA {indexedA=index, contextA=ctx}) (Initialize (IndexedProperty ind arg) toterm) = [(pm {indexedA=newindex}, "")]
                                                                         where
                                                                             newvalue = termValue pm toterm
                                                                             argind = toIndex ctx $ termValue pm arg
                                                                             newindex = (Array.//) index [((ind, argind), newvalue)]
executeA' pm@(PMA {factsA=facts}) (Initialize term toterm) = [(pm {factsA=newfacts}, "")]
                                                                         where
                                                                             newvalue = termValue pm toterm
                                                                             key = propName pm term
                                                                             name = head key
                                                                             args = tail key
                                                                             current = Map.findWithDefault Map.empty name facts
                                                                             newvaluemap = Map.alter (const $ Just newvalue) args current
                                                                             newfacts = Map.alter (const $ Just newvaluemap) name facts
executeA' pm@(PMA {indexedA=index, contextA=ctx}) (Set (IndexedProperty ind arg) toterm) = [(pm {indexedA=newindex}, "")]
                                                                         where
                                                                             newvalue = termValue pm toterm
                                                                             argind = toIndex ctx $ termValue pm arg
                                                                             newindex = (Array.//) index [((ind, argind), newvalue)]
executeA' pm@(PMA {factsA=facts}) (Set term toterm) = [(pm {factsA=newfacts},"")]
                                                                  where
                                                                     newvalue = termValue pm toterm
                                                                     key = propName pm term
                                                                     name = head key
                                                                     args = tail key
                                                                     current = Map.findWithDefault Map.empty name facts
                                                                     newvaluemap = Map.alter (const $ Just newvalue) args current
                                                                     newfacts = Map.alter (const $ Just newvaluemap) name facts
executeA' pm@(PMA {indexedA=index, contextA=ctx}) (UnSet (IndexedProperty ind arg)) = error "Can't unset indexed property"
executeA' pm@(PMA {factsA=facts}) (UnSet term) = [(pm {factsA=newfacts},"")]
                                                             where
                                                                     key = propName pm term
                                                                     name = head key
                                                                     args = tail key
                                                                     current = Map.findWithDefault Map.empty name facts
                                                                     newvaluemap = Map.alter (const $ Nothing) args current
                                                                     newfacts = Map.alter (const $ Just newvaluemap) name facts
                                                                     
executeA' pm (If condition action) = if pm `interpretsA` condition then executeA' pm action else [(pm,"")]
executeA' pm (Precondition condition) = if pm `interpretsA` condition then [(pm,"")] else []
executeA' pm (IfElse condition ifbranch elsebranch) = if pm `interpretsA` condition then executeA' pm ifbranch else executeA' pm elsebranch
executeA' pm (PublicIfElse actors condition ifbranch elsebranch) = if pm `interpretsA` condition then executeA' pm ifbranch else executeA' pm elsebranch
executeA' pm (Public actors action) = [(pm1 {appearanceA=(makeAppWithRehash (App app locked) actors (makeMap (appearance app) acts))},out) | (pm1@(PMA {appearanceA=(App app locked),actorsA=acts}),out) <- executeA' pm action]
                                                          where
                                                              appearance app a = if a `elem` actors then (map fst $ concat [executeA' w (Public actors action) | w <-  Map.findWithDefault [] a app]) 
                                                                                                    else Map.findWithDefault [] a app
                                                              
executeA' pm@(PMA {weightA=w}) (AddWeight delta) = [(pm {weightA=(w+delta)}, "")]
executeA' _ (DEL _) = []
executeA' pm (OstariPrint output) = [(pm,intercalate " " $ map toOutput output)]

makeAppWithRehash :: (AbstractActionType a, GenArray a b) => Appearances a (b (Int,Int) a) -> [a] -> (Map.Map a [PointedModelA a (b (Int,Int) a)]) -> Appearances a (b (Int,Int) a)
makeAppWithRehash (App oldapp locked) actors newapp = if null actors then initial else foldl rehashLocks initial actors
                                                   where
                                                      initial = App newapp locked

performLocking :: (AbstractActionType a, GenArray a b) => Context -> [a] -> PointedModelA a (b (Int,Int) a) -> PointedModelA a (b (Int,Int) a)
performLocking ctx props pm@(PMA {appearanceA=app}) = pm {appearanceA=(lockProperties ctx app props)}

ensureActors :: AbstractActionType a => Appearances a (b (Int,Int) a) -> [a] -> Appearances a (b (Int,Int) a)
ensureActors app [] = app
ensureActors oldapp@(App app index) (x:xs) = ensureActors newapp xs
                                   where
                                       newapp = if Map.member x index then oldapp else (App app $ Map.insert x Map.empty index)
                                                      
lockProperties :: (AbstractActionType a, GenArray a b) => Context -> Appearances a (b (Int,Int) a) -> [a] -> Appearances a (b (Int,Int) a)
lockProperties _ app [] = app
lockProperties ctx app (p:ps) = lockProperties ctx newapp ps
                             where
                                 argtypes = getList (getSignatures ctx) p
                                 argcombinations = sequence [getValues ctx arg | arg <- argtypes]
                                 newapp = lockProperty ctx (ensureActors app $ map (fromStringValue ctx) $ actors ctx) p argcombinations

lockProperty :: (AbstractActionType a, GenArray a b) => Context -> Appearances a (b (Int,Int) a) -> a -> [[a]] -> Appearances a (b (Int,Int) a)
lockProperty ctx (App appearances locked) prop args = (App appearances $ Map.mapWithKey updateActorMap locked)
                                              where
                                                 updateActorMap a m = Map.insert prop (splitmap a) m
                                                 splitmap a = makeMap (matching a) args
                                                 matching actor a = filter (\w -> w `interpretsA` (Equal (PropertyN prop $ map Constant $ tail a) (Constant $ head a))) $ Map.findWithDefault [] actor appearances
                                                 
extractValue (Just x) = x

rehashLocks :: (AbstractActionType a, GenArray a b) => Appearances a (b (Int,Int) a) -> a -> Appearances a (b (Int,Int) a)
rehashLocks (App appearances locked) actor = if Map.member actor locked then (App appearances $ Map.alter updateActorMap actor locked) else (App appearances locked)
                                              where
                                                 updateActorMap m = Just $ Map.mapWithKey (updatePropMap) $ extractValue m
                                                 updatePropMap p m = Map.mapWithKey (updateSplitMap p) m
                                                 updateSplitMap p args old = filter (\w -> w `interpretsA` (Equal (PropertyN p $ map Constant $ tail args) (Constant $ head args))) $ Map.findWithDefault [] actor appearances                                                 



makePropertyIndex :: (AbstractActionType a, GenArray a b) => a -> PointedModelA a (b (Int,Int) a) -> PointedModelA a (b (Int,Int) a)
makePropertyIndex property pm@(PMA {appearanceA=(App app locked), factsA=facts, staticsA=statics, indexedA=index, actorsA=actors, contextA=ctx})  = pm {appearanceA=newapp, factsA=newfacts, staticsA=newstatics, indexedA=newindex}
                                 where
                                    newapp = makeAppWithRehash (App app locked) actors newmap
                                    newmap = Map.map (\pms -> map (makePropertyIndex property) pms) app
                                    newfacts = Map.delete property facts
                                    newstatics = Map.delete property statics
                                    source = Map.union facts statics
                                    indx = [((toIndex ctx property, toIndex ctx $ head args), val) | (args,val) <- Map.toList $ Map.findWithDefault Map.empty property source]
                                    newindex = (Array.//) index indx

makeIndex :: (AbstractActionType a, GenArray a b) => PointedModelA a (b (Int,Int) a) -> PointedModelA a (b (Int,Int) a)
makeIndex pm@(PMA {contextA=ctx, appearanceA=(App app locked)}) = foldl (flip makePropertyIndex) initial properties
                                 where
                                     indices = getSetByName ctx "Indices"
                                     valid = Map.filter (\args -> (length args == 2) && (allindices (getSet ctx $ args!!1))) $ getSignatures ctx
                                     allindices vals = and [v `elem` indices | v <- vals]
                                     objindices = map (toIndex ctx) indices
                                     properties = Map.keys valid
                                     propindices = map (toIndex ctx) properties
                                     index = Array.array ((minimum propindices, minimum objindices),(maximum propindices,maximum objindices)) [((i,j),defaultValue) | i <- propindices, j <- objindices]
                                     initial = pm {appearanceA=tmpapp, indexedA=index, contextA=updateContextWithIndices ctx properties}
                                     tmpapp = (App (Map.map (\ms -> map (\m -> m {appearanceA=tmpapp, indexedA=index, contextA=updateContextWithIndices ctx properties}) ms) app) locked)

replaceIndexedProperties :: AbstractActionType a => Context -> AbstractAction a -> AbstractAction a
replaceIndexedProperties ctx (SuspectAction actor action) = SuspectAction actor $ replaceIndexedProperties ctx action
replaceIndexedProperties ctx (PublicArgument varname setname action) = PublicArgument varname setname $ replaceIndexedProperties ctx action
replaceIndexedProperties ctx (SecretArgument actors varname setname action) = SecretArgument actors varname setname $ replaceIndexedProperties ctx action
replaceIndexedProperties ctx (Inform actors action) = Inform actors $ replaceIndexedPropertiesP ctx action
replaceIndexedProperties ctx (Suspect actors action) = Suspect actors $ replaceIndexedPropertiesP ctx action
replaceIndexedProperties ctx (Sequence actions) = Sequence $ map (replaceIndexedProperties ctx) actions
replaceIndexedProperties ctx (Set term value) = Set (replaceIndexedPropertiesT ctx  term) (replaceIndexedPropertiesT ctx value)
replaceIndexedProperties ctx (Initialize term value) = Initialize (replaceIndexedPropertiesT ctx  term) (replaceIndexedPropertiesT ctx value)
replaceIndexedProperties ctx (UnSet term) = UnSet (replaceIndexedPropertiesT ctx  term)
replaceIndexedProperties ctx (If condition action) = If (replaceIndexedPropertiesP ctx  condition) $ replaceIndexedProperties ctx action
replaceIndexedProperties ctx (Precondition condition) = Precondition $ replaceIndexedPropertiesP ctx  condition
replaceIndexedProperties ctx (IfElse condition ifaction elseaction) = IfElse (replaceIndexedPropertiesP ctx condition) (replaceIndexedProperties ctx ifaction) $ replaceIndexedProperties ctx elseaction
replaceIndexedProperties ctx (PublicIfElse actors condition ifaction elseaction) = PublicIfElse actors (replaceIndexedPropertiesP ctx condition) (replaceIndexedProperties ctx ifaction) $ replaceIndexedProperties ctx  elseaction
replaceIndexedProperties ctx (Public actors inner) = Public actors $ replaceIndexedProperties ctx inner
replaceIndexedProperties ctx (DEL action) = DEL action
replaceIndexedProperties ctx (AddWeight w) = AddWeight w
replaceIndexedProperties ctx (OstariPrint s) = OstariPrint s

replaceIndexedPropertiesP :: AbstractActionType a => Context -> Predicate a -> Predicate a
replaceIndexedPropertiesP ctx (Forall var set pred) = Forall var set $ replaceIndexedPropertiesP ctx pred
replaceIndexedPropertiesP ctx (Each var set pred) = Each var set $ replaceIndexedPropertiesP ctx pred
replaceIndexedPropertiesP ctx (Which var set pred) = Which var set $ replaceIndexedPropertiesP ctx pred
replaceIndexedPropertiesP ctx (Exists var set pred) = Exists var set $ replaceIndexedPropertiesP ctx pred
replaceIndexedPropertiesP ctx (Equal t1 t2) = Equal (replaceIndexedPropertiesT ctx t1) $ replaceIndexedPropertiesT ctx t2
replaceIndexedPropertiesP ctx (NotEqual t1 t2) = NotEqual (replaceIndexedPropertiesT ctx t1) $ replaceIndexedPropertiesT ctx t2
replaceIndexedPropertiesP ctx (AndP t1 t2) = AndP (replaceIndexedPropertiesP ctx t1) $ replaceIndexedPropertiesP ctx t2
replaceIndexedPropertiesP ctx (OrP t1 t2) = OrP (replaceIndexedPropertiesP ctx t1) $ replaceIndexedPropertiesP ctx t2
replaceIndexedPropertiesP ctx (IsSet t1) = IsSet $ replaceIndexedPropertiesT ctx t1
replaceIndexedPropertiesP ctx (IsUnSet t1) = IsUnSet $ replaceIndexedPropertiesT ctx t1
replaceIndexedPropertiesP ctx (Believes a p) = Believes a $ replaceIndexedPropertiesP ctx p
replaceIndexedPropertiesP ctx (StrongBelieves a p) = StrongBelieves a $ replaceIndexedPropertiesP ctx p
replaceIndexedPropertiesP ctx (Probably op prob a p) = Probably op prob a $ replaceIndexedPropertiesP ctx p
replaceIndexedPropertiesP ctx (WeightedProbably w op prob a p) = WeightedProbably w op prob a $ replaceIndexedPropertiesP ctx p
replaceIndexedPropertiesP ctx (NotBelieves a p) = NotBelieves a $ replaceIndexedPropertiesP ctx p

replaceIndexedPropertiesT :: AbstractActionType a => Context -> Term a -> Term a
replaceIndexedPropertiesT ctx (Variable name) = Variable name
replaceIndexedPropertiesT ctx (Property name arg) = if name `elem` (getIndices ctx) then (IndexedProperty (toIndex ctx name) $ replaceIndexedPropertiesT ctx arg) else Property name $ replaceIndexedPropertiesT ctx arg
replaceIndexedPropertiesT ctx (Property2 name arg1 arg2) = if name `elem` (getIndices ctx) then error "cannot index property with two arguments" else Property2 name (replaceIndexedPropertiesT ctx arg1) $ replaceIndexedPropertiesT ctx arg2
replaceIndexedPropertiesT ctx (PropertyN name args) = if name `elem` (getIndices ctx) then (IndexedProperty (toIndex ctx name) $ replaceIndexedPropertiesT ctx $ head args) else PropertyN name $ map (replaceIndexedPropertiesT ctx) args
replaceIndexedPropertiesT ctx (Constant value) = Constant value




