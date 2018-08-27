{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE BangPatterns #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE FlexibleContexts #-}
module AbstractActions where

import BaseTypes
import Baltag hiding (sumAction, productAction, cleanComposition, cleanChoice, cleanSum, cleanProduct, cleanAnd, cleanOr)
import BaltagString
import Data.List
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.Array.IArray as Array
import qualified Data.Array.Unboxed as UArray



data Term a = Variable a
          | Property a (Term a)
          | Property2 a (Term a) (Term a)
          | PropertyN a [Term a]
          | Constant a
          | IndexedProperty Int (Term a)
           deriving (Show, Read, Eq)
           
termName :: AbstractActionType a => Term a -> a
termName (Variable name) = name
termName (Property name _) = name
termName (Property2 name _ _) = name
termName (PropertyN name _) = name
termName (Constant name) = name
termName (IndexedProperty name _) = indexToUnique name

termArgs (Property name arg) = [arg]
termArgs (Property2 name arg1 arg2) = [arg1, arg2]
termArgs (PropertyN name args) = args
termArgs (IndexedProperty _ arg) = [arg]
termArgs _ = []

getArgs :: AbstractActionType a => Term a -> [a]
getArgs (Property _ arg) = [termName arg]
getArgs (Property2 _ arg1 arg2) = map termName [arg1, arg2]
getArgs (PropertyN _ args) = map termName args
getArgs (IndexedProperty _ arg) = [termName arg]
getArgs _ = []


{- 
   The difference between "Each" and "Forall" is:
      - "Forall" refers to the conjunction of all possibilities (e.g. "all cards in your hand are red")
      - "Each" refers to the disjunction of the conjunction of all subsets of possibilities (e.g. "which subset of your hand is red")
   In other words, "Forall" is true when something holds for all values, while "each" will tell you for which values it holds
   
   Similarly, the difference between "Exists" and "Which" is:
      - "Exists" refers to the disjunction of all possibilities (e.g. "there is a red card in your hand")
      - "Which" refers to a particular exemplar (e.g. "this is a red card in your hand")
   In other words, "Exists" is true when something holds for some value, while "which" will tell you ONE such value (this is particularly
   useful if it is known that something can only hold for one value ... e.g. there is a card such that the first card in your hand is that
   card ... "which" will tell you exactly which one that is)
-}
data Predicate a = Forall a a (Predicate a)
                 | Each a a (Predicate a)
                 | Exists a a (Predicate a)
                 | Which a a (Predicate a)
                 | Equal (Term a) (Term a)
                 | NotEqual (Term a) (Term a)
                 | AndP (Predicate a) (Predicate a)
                 | OrP (Predicate a) (Predicate a)
                 | NotP (Predicate a)
                 | IsSet (Term a)
                 | IsUnSet (Term a)
                 | Believes a (Predicate a)
                 | NotBelieves a (Predicate a)
                 | StrongBelieves a (Predicate a)
                 | StrongNotBelieves a (Predicate a)
                 | Probably Op Float a (Predicate a) -- true iff more/less than a certain percentage of worlds models the condition
                 | WeightedProbably a Op Float a (Predicate a) -- true iff more/less than a certain percentage of worlds models the condition. Worlds are weighted by the inverse of one plus the sum of all (numerical) values that the given property has in the world 
                 deriving (Show, Read, Eq)

data AbstractAction a = Sequence [AbstractAction a]
                  | PublicArgument a a (AbstractAction a)
                  | SecretArgument [a] a a (AbstractAction a)
                  | Inform [a] (Predicate a)
                  | Suspect [a] (Predicate a)
                  | Initialize (Term a) (Term a)
                  | Set (Term a) (Term a)
                  | UnSet (Term a)
                  | If (Predicate a) (AbstractAction a)
                  | Precondition (Predicate a)
                  | IfElse (Predicate a) (AbstractAction a) (AbstractAction a)
                  | PublicIfElse [a] (Predicate a) (AbstractAction a) (AbstractAction a)
                  | Public [a] (AbstractAction a)
                  | DEL (Action String)
                  | OstariPrint [String]
                  | PartiallyVisibleAction [a] (AbstractAction a) [(AbstractAction a)] String
                  | SuspectAction a (AbstractAction a)
                  | AddWeight Float
                  deriving (Show, Read, Eq)
                  
data BeliefLayers a = BL [a]
                  deriving (Show)

pvname (SuspectAction a act) = (show a) ++ " suspects " ++ (pvname act)
pvname (PartiallyVisibleAction _ _ _ name) = name
pvname _ = "unknown"

addBL b (BL a) = (BL (b:a))

emptyBL (BL a) = null a

matches _ [] [] = True
matches _ [] _ = False
matches _ _ [] = False
matches wc (x:xs) (y:ys) | x == wc || y == wc || x == y = matches wc xs ys
                         | otherwise                    = False


findTermValue :: AbstractActionType a => a -> [a] -> Map.Map a (Map.Map [a] a) -> a
findTermValue name args m = Map.findWithDefault defaultValue args $ Map.findWithDefault Map.empty name m
  
type SArray = Array.Array (Int,Int) String
type IArray = UArray.UArray (Int,Int) Int
type GenArray a b = (UArray.IArray b a)
  
class (Ord a, Eq a, Show a, ActionType a) => AbstractActionType a where
    defaultValue :: a
    unknownValue :: a
    wildcard :: a
    randomProp :: a
    weightvalue :: a
    getSets :: Context -> Map.Map a [a] 
    getSet :: Context -> a -> [a]
    getSet ctx name = Map.findWithDefault [] name $ getSets ctx
    getSetByName :: Context -> String -> [a]
    getSetByName ctx name = getSet ctx $ fromStringValue ctx name
    getSignatures :: Context -> Map.Map a [a]
    toStringMap :: Context -> Map.Map a a -> Map.Map String String
    toStringValue :: Context -> a -> String
    fromStringMap :: Context -> Map.Map String String -> Map.Map a a
    fromStringValue :: Context -> String -> a
    fromStringAction :: Context -> AbstractAction String -> AbstractAction a
    fromStringPredicate :: Context -> Predicate String -> Predicate a
    nop :: AbstractAction a
    tautology :: Predicate a
    getPhaseName :: Context -> a
    getGameName :: Context -> a
    toIndex :: Context -> a -> Int
    fromIndex :: Context -> Int -> a
    getIndices :: Context -> [a]
    updateContextWithIndices :: Context -> [a] -> Context
    indexToUnique :: Int -> a
    isStaticProp :: Context -> a -> Bool
    isIndexedProp :: Context -> a -> Bool
    getBValueA :: (UArray.IArray b a) => Context -> PointedModelA a (b (Int,Int) a) -> Term a -> Int -> a
    getBValueA ctx pm !(Constant v) _ = v
    getBValueA ctx pm !(Variable v) _ = v
    getBValueA ctx pm !(IndexedProperty ind arg) _ = (UArray.!) index  (ind, toIndex ctx $ termValue pm arg)
                                         where 
                                            ctx = contextA pm
                                            index = indexedA pm
    getBValueA ctx pm t val = if name == randomProp then value
                               else if Map.member name $ staticsA pm then findTermValue name args $ staticsA pm else findTermValue name args $ factsA pm
                           where
                              name = termName t
                              args = [getBValueA ctx pm arg val | arg <- termArgs t]
                              values = getSet ctx $ termValue pm $ head $ termArgs t
                              value = values!!(val `mod` (length values))
    termValue :: (UArray.IArray b a) => PointedModelA a (b (Int,Int) a) -> Term a -> a
    termValue pm !(Constant v) = v
    termValue pm !(Variable v) = v
    termValue pm !(IndexedProperty ind arg) = (UArray.!) index  (ind, toIndex ctx $ termValue pm arg)
                                         where 
                                            ctx = contextA pm
                                            index = indexedA pm
    termValue pm t = if Map.member name $ staticsA pm then findTermValue name args $ staticsA pm else findTermValue name args $ factsA pm
                   where
                      name = termName t
                      args = [termValue pm arg | arg <- termArgs t]
    resolveBindingsString :: Context -> Term a -> String -> String -> Term a
    showCall :: Context -> String -> [a] -> String
    showCall ctx name args = formatCall name $ map (toStringValue ctx) args
    

    
instance AbstractActionType String where
    defaultValue = ""
    unknownValue = "unknown"
    wildcard = "*"
    weightvalue = "weight"
    randomProp = "random"
    getSets = sets
    getSignatures = signatures
    toStringMap _ = id
    toStringValue _ = id
    fromStringMap _ = id
    fromStringValue _ = id
    fromStringAction _ = id
    fromStringPredicate _ = id
    nop = Sequence []
    tautology = Equal (Constant "a") (Constant "a")
    getPhaseName _ = "phase"
    getGameName _ = "game"
    toIndex = strToInt
    fromIndex = intToStr
    getIndices = indexed
    updateContextWithIndices ctx ind = ctx {indexed=ind, indexedi=map (strToInt ctx) ind}
    indexToUnique = show
    isStaticProp ctx n = Map.member n (static_predicates ctx)
    isIndexedProp ctx n = n `elem` (indexed ctx)
    resolveBindingsString ctx t var val = resolveVarsTerm (Map.singleton var val) t
   
    
    
instance AbstractActionType Int where
    defaultValue = (-1)
    unknownValue = (-1)
    wildcard = (-2)
    weightvalue = (-3)
    randomProp = (-4)
    getSets = setsi
    getSignatures = signaturesi
    toStringMap ctx m = Map.mapKeys (intToStr ctx) $ Map.map (intToStr ctx) m
    toStringValue = intToStr
    fromStringMap ctx m = Map.mapKeys (strToInt ctx) $ Map.map (strToInt ctx) m
    fromStringValue = strToInt
    fromStringAction = optimizeAction
    fromStringPredicate = optimizePredicate
    tautology = Equal (Constant 0) (Constant 0)
    nop = Sequence []
    getPhaseName ctx = strToInt ctx "phase"
    getGameName ctx = strToInt ctx "game"
    toIndex ctx = id
    fromIndex ctx = id
    getIndices = indexedi
    updateContextWithIndices ctx ind = ctx {indexed=map (intToStr ctx) ind, indexedi=ind}
    indexToUnique = id
    isStaticProp ctx n = Map.member (toStringValue ctx n) (static_predicates ctx)
    isIndexedProp ctx n = n `elem` (indexedi ctx)
    
    termValue pm !(Constant v) = v
    termValue pm !(Variable v) = v
    termValue pm !(IndexedProperty ind (Constant c)) = getv pm (IndexedProperty ind (Constant c))
    termValue pm !(IndexedProperty ind (Variable v)) = getv pm (IndexedProperty ind (Variable v))
    termValue pm !(IndexedProperty ind arg) = (Array.!) index  (ind, termValue pm arg)
                                         where 
                                            index = indexedA pm
    termValue pm !t = if Map.member name $ staticsA pm then findTermValue name args $ staticsA pm else findTermValue name args $ factsA pm
                   where
                      name = termName t
                      args = [termValue pm arg | arg <- termArgs t]
    resolveBindingsString ctx t var val = resolveVarsTerm (Map.singleton (strToInt ctx var) (strToInt ctx val)) t

getv pm !(IndexedProperty ind (Constant c)) = (Array.!) (indexedA pm)  (ind, c)
getv pm !(IndexedProperty ind (Variable v)) = (Array.!) (indexedA pm)  (ind, v)
                      

instance AbstractActionType a => Eq (BeliefLayers a) where
   (BL a) == (BL b) = if (a == b) then True else matches wildcard a b
   
instance AbstractActionType a => Ord (BeliefLayers a) where
   (BL a) `compare` (BL b) = if (BL a) == (BL b) then EQ else a `compare` b
 
 
data ExecutionType = ExecPrint String [String] 
                   | Execute String [String] [String] 
                   | Query (Predicate String)
                   | Quality (Predicate String)
                   | QueryWhich String String (Predicate String)
                   | QueryEach String String (Predicate String)
                   | Plan (Predicate String) [String] 
                   | PlanAgent (Predicate String) [String] String
                   | Play [(String,String,[String])]
                   | Lock [String]
                   | Prompt

getChanges :: AbstractActionType a => AbstractAction a -> Set.Set (BeliefLayers a,a)
getChanges (Sequence actions) = Set.unions $ map getChanges actions
getChanges (PublicArgument _ _ a) = getChanges a
getChanges (SecretArgument _ _ _ a) = getChanges a
getChanges (Inform actors a) = Set.fromList $ [(addBL act b,ch) | (b,ch) <- Set.toList $ getReferences a, act <- actors]
getChanges (Suspect actors a) = Set.fromList $ [(addBL act b,ch) | (b,ch) <- Set.toList $ getReferences a, act <- actors]
getChanges (Initialize t _) = Set.singleton (BL [],termName t)
getChanges (Set t _) = Set.singleton (BL [],termName t)
getChanges (UnSet t) = Set.singleton (BL [],termName t)
getChanges (If _ a) = getChanges a
getChanges (IfElse _ a b) = Set.union (getChanges a) $ getChanges b
getChanges (PublicIfElse actors c a b) = Set.union changes $ Set.unions [Set.map (\(b,ch) -> (addBL act b,ch)) $ Set.union changes refs | act <- actors]
                                      where
                                          changes = Set.union (getChanges a) $ getChanges b
                                          refs = getReferences c
getChanges (Public actors a) = Set.union changes $ Set.unions [Set.map (\(b,ch) -> (addBL act b,ch)) $ Set.union changes reqs | act <- actors] 
                            where
                                changes = getChanges a
                                reqs = getRequirements a
getChanges (PartiallyVisibleAction actors a b _) = if null b then getChanges a else (Set.union (getChanges a) $ Set.map (\(bel,ch) -> (addBL wildcard bel,ch)) $ Set.union (getChanges a) $ getRequirements a)
getChanges (SuspectAction actor a) = Set.map (\(b,ch) -> (addBL actor b,ch)) $ Set.union (getChanges a) $ getRequirements a
getChanges (AddWeight _) = Set.singleton (BL [], weightvalue)
getChanges _ = Set.empty


getRequirements :: AbstractActionType a => AbstractAction a -> Set.Set (BeliefLayers a,a)
getRequirements (Sequence actions) = Set.unions $ map getRequirements actions
getRequirements (PublicArgument _ _ a) = getRequirements a
getRequirements (SecretArgument _ _ _ a) = getRequirements a
getRequirements (Inform actors a) = Set.fromList [(addBL act b,ch) | (b,ch) <- Set.toList $ getReferences a, act <- actors]
getRequirements (Suspect actors a) = Set.fromList [(addBL act b,ch) | (b,ch) <- Set.toList $ getReferences a, act <- actors]
getRequirements (Initialize t t1) = Set.union (termReferences t) (termReferences t1)
getRequirements (Set t t1) = Set.union (termReferences t) (termReferences t1)
getRequirements (UnSet t) = termReferences t
getRequirements (If c a) = Set.union (getReferences c) $ getRequirements a
getRequirements (Precondition c) = getReferences c
getRequirements (IfElse c a b) = Set.union (getReferences c) $ Set.union (getRequirements a) $ getRequirements b
getRequirements (PublicIfElse _ c a b) = Set.union (getReferences c) $ Set.union (getRequirements a) $ getRequirements b
getRequirements (Public actors a) = Set.union refs $ Set.unions [Set.map (\(b,ch) -> (addBL act b,ch)) refs | act <- actors] 
                            where
                                refs = getRequirements a
getRequirements (PartiallyVisibleAction actors a b _) = Set.union (getRequirements a) $ Set.unions [ Set.map (\(bel,ch) -> (addBL act bel,ch)) $ getRequirements a | act <- actors]
getRequirements (SuspectAction actor a) = Set.map (\(b,ch) -> (addBL actor b,ch)) $ getRequirements a
getRequirements (AddWeight _) = Set.singleton (BL [], weightvalue)
getRequirements _ = Set.empty

removeVariable :: AbstractActionType a => a -> BeliefLayers a -> BeliefLayers a
removeVariable _ (BL []) = BL []
removeVariable v (BL (x:xs)) | x == v    = addBL wildcard $ removeVariable v (BL xs)
                             | otherwise = addBL x $ removeVariable v (BL xs)

fixRef :: AbstractActionType a => a -> (BeliefLayers a,a) -> (BeliefLayers a,a)
fixRef v (bel,pred) = (removeVariable v bel, pred)

getReferences :: AbstractActionType a => Predicate a -> Set.Set (BeliefLayers a, a)
getReferences (Forall v _ p) = Set.map (fixRef v) $ getReferences p
getReferences (Each v _ p) = Set.map (fixRef v) $ getReferences p
getReferences (Exists v _ p) = Set.map (fixRef v) $ getReferences p
getReferences (Which v _ p) = Set.map (fixRef v) $ getReferences p
getReferences (Equal t1 t2) = Set.union (termReferences t1) $ termReferences t2
getReferences (NotEqual t1 t2) = Set.union (termReferences t1) $ termReferences t2
getReferences (AndP a b) = Set.union (getReferences a) $ getReferences b
getReferences (OrP a b) = Set.union (getReferences a) $ getReferences b
getReferences (NotP a) = getReferences a
getReferences (IsSet t) = termReferences t
getReferences (IsUnSet t) = termReferences t
getReferences (Believes a p) = Set.map (\(b,ref) -> (addBL a b,ref)) $ getReferences p
getReferences (NotBelieves a p) = Set.map (\(b,ref) -> (addBL a b,ref)) $ getReferences p
getReferences (StrongBelieves a p) = Set.map (\(b,ref) -> (addBL a b,ref)) $ getReferences p
getReferences (Probably _ _ a p) = Set.map (\(b,ref) -> (addBL a b,ref)) $ getReferences p
getReferences (WeightedProbably w _ _ a p) = Set.union (Set.singleton (BL [a],weightvalue)) $ Set.map (\(b,ref) -> (addBL a b,ref)) $ getReferences p

termReferences :: AbstractActionType a => Term a -> Set.Set (BeliefLayers a, a)
termReferences (Property p arg) = Set.union (termReferences arg) $ Set.singleton (BL [],p)
termReferences (Property2 p a b) = Set.union (termReferences a) $ Set.union (termReferences b) $ Set.singleton (BL [],p)
termReferences (PropertyN p args) = Set.union (Set.singleton (BL [],p)) $ Set.unions $ map (termReferences) args
termReferences (IndexedProperty p arg) = Set.union (termReferences arg) $ Set.singleton (BL [],indexToUnique p)
termReferences _ = Set.empty

getArgNames :: AbstractAction a -> [a]
getArgNames (PublicArgument var _ act) = var:(getArgNames act)
getArgNames (SecretArgument _ var _ act) = var:(getArgNames act)
getArgNames _ = []

getArgTypes :: AbstractAction a -> [a]
getArgTypes (PublicArgument _ set act) = set:(getArgTypes act)
getArgTypes (SecretArgument _ _ set act) = set:(getArgTypes act)
getArgTypes _ = []

getActionArgs :: AbstractAction a -> [(a,a)]
getActionArgs (PublicArgument var set act) = (var,set):(getActionArgs act)
getActionArgs (SecretArgument _ var set act) = (var,set):(getActionArgs act)
getActionArgs _ = []
          
getReturnType :: AbstractActionType a => Context -> a -> a
getReturnType ctx name = head (getList (getSignatures ctx) name)


getList :: AbstractActionType a => Map.Map a [a] -> a -> [a]
getList typemap name = Map.findWithDefault [] name typemap

getValues :: AbstractActionType a => Context -> a -> [a]
getValues ctx setname = Map.findWithDefault [] setname $ getSets ctx

{-
At some point during execution it may happen that certain properties won't change in the appearances anymore, but will be required for lots of queries later.
By ``locking'' these properties a second map is created that can be used to look up possible worlds by the value of these properties.
For example, if there are 10 000 possible worlds, and the color of some object is red, green or blue in some of them, it may be desirable to query if the object being blue would imply
some other property, e.g. ``B (a) (color(object) != blue or ....)''. Instead of iterating over all possible worlds, the ones not matching the first condition can be looked up and the
second condition only checked on the others. Additionally, this makes it possible to quickly compute P and W queries involving the locked properties.

This second, locked map is the following:
actor -> property -> arguments+value -> worlds
-}
data Appearances a b = App (Map.Map a [PointedModelA a b]) (Map.Map a (Map.Map a (Map.Map [a] [PointedModelA a b])))

getAppearanceMap (App m _) = m
getLockedAppearance (App _ l) = l


data PointedModelA a b = PMA { appearanceA :: Appearances a b,
                             factsA :: Map.Map a (Map.Map [a] a),
                             staticsA :: Map.Map a (Map.Map [a] a),
                             indexedA :: b,
                             actorsA :: [a],
                             contextA :: Context,
                             weightA :: Float }
                             


toPMAInt :: PointedModelA String SArray -> PointedModelA Int IArray
toPMAInt (PMA (App appearance locked) facts statics ind actors ctx weight) = (PMA newapp (convertMap facts) (convertMap statics) index (map (strToInt ctx) actors) ctx weight)
                                                          where
                                                             newapp = App (Map.mapKeys (strToInt ctx) $ Map.map (map toPMAInt) appearance) Map.empty
                                                             convertMap m = Map.mapKeys (strToInt ctx) $ Map.map (convertInner) m
                                                             convertInner m = Map.mapKeys (map (strToInt ctx)) $ Map.map (strToInt ctx) m
                                                             index = Array.array (Array.bounds ind) $ map (\(i,v) -> (i,strToInt ctx v)) $ Array.assocs ind

fromPMAInt :: (GenArray Int b) => PointedModelA Int (b (Int,Int) Int) -> PointedModelA String SArray
fromPMAInt (PMA (App appearance locked) facts statics ind actors ctx weight) = (PMA newapp (convertMap facts) (convertMap statics) index (map (intToStr ctx) actors) ctx weight)
                                                          where
                                                             newapp = App (Map.mapKeys (intToStr ctx) $ Map.map (map fromPMAInt) appearance) Map.empty
                                                             convertMap m = Map.mapKeys (intToStr ctx) $ Map.map (convertInner) m
                                                             convertInner m = Map.mapKeys (map (intToStr ctx)) $ Map.map (intToStr ctx) m                                                             
                                                             index = Array.array (Array.bounds ind) $ map (\(i,v) -> (i,intToStr ctx v)) $ Array.assocs ind


toProperty :: Context -> AtProp Int -> [String]
toProperty ctx (Predicate name args) = map (intToStr ctx) (name:(init args))

toPropertyValue :: Context -> AtProp Int -> String
toPropertyValue ctx (Predicate name args) = intToStr ctx $ last args

calculateWeight :: Map.Map [String] String -> Float
calculateWeight f = fromIntegral $ sum weights
              where
                  weights = [toInt x | (_,x) <- Map.toList f]
                  
toPropAssignment :: AbstractActionType a => [([a],a)] -> Map.Map a (Map.Map [a] a)
toPropAssignment values = Map.fromList [(n,Map.fromList $ binvalues n) | n <- propnames]
                       where
                           bins = map (\(n,v) -> (head n,(tail n, v))) values
                           binvalues b = [(args,val) | (name,(args,val)) <- bins, name == b]
                           propnames = nub $ map fst bins

fromPM :: PointedModel -> PointedModelA String SArray
fromPM (PM app facts actors ctx _) = (PMA newapp dynamicm (toPropAssignment static) index actors ctx (calculateWeight $ Map.findWithDefault Map.empty "liar" dynamicm))
                                  where
                                      newapp = App (Map.map (map fromPM) app) Map.empty
                                      assignments = [(toProperty ctx atprop, toPropertyValue ctx atprop) | atprop <- Set.toList facts]
                                      statics = static_predicates ctx
                                      (static,dynamic) = partition (\(prop,_) -> Map.member (head prop) statics) assignments
                                      dynamicm = toPropAssignment dynamic
                                      index = Array.listArray ((1,1),(2,2)) [defaultValue, defaultValue, defaultValue, defaultValue]
   

toPropertyInt :: AtProp Int -> [Int]
toPropertyInt (Predicate name args) = (name:(init args))

toPropertyValueInt :: AtProp Int -> Int
toPropertyValueInt (Predicate name args) = last args

calculateWeightInt :: Context -> Map.Map [Int] Int -> Float
calculateWeightInt ctx f = fromIntegral $ sum weights
              where
                  weights = [toInt $ intToStr ctx x | (_,x) <- Map.toList f]
                     
fromPMInt :: PointedModel -> PointedModelA Int IArray
fromPMInt (PM app facts actors ctx _) = (PMA newapp dynamicm (toPropAssignment static) index (map (strToInt ctx) actors) ctx (calculateWeightInt ctx $ Map.findWithDefault Map.empty (strToInt ctx "liar") dynamicm))
                                  where
                                      newapp = App (Map.mapKeys (strToInt ctx) $ Map.map (map fromPMInt) app) Map.empty
                                      assignments = [(toPropertyInt atprop, toPropertyValueInt atprop) | atprop <- Set.toList facts]
                                      statics = static_predicates ctx
                                      (static,dynamic) = partition (\(prop,_) -> Map.member (intToStr ctx $ head prop) statics) assignments
                                      dynamicm = toPropAssignment dynamic
                                      index = Array.listArray ((1,1),(2,2)) [defaultValue, defaultValue, defaultValue, defaultValue]

--(PM (Map.Map String [PointedModel]) (Set.Set (AtProp Int)) [String] Context (Map.Map [Int] (Set.Set Int))


getValue :: Context -> PointedModel -> String -> [String] -> String
getValue ctx pm name args = getValue' ctx pm (convert name) $ map convert args
                         where
                               ids = makeIDMap ctx
                               convert x = Map.findWithDefault (-1) x ids
                               
getValue' :: Context -> PointedModel -> Int -> [Int] -> String
getValue' ctx (PM app fact _ _ _) name args = convert value
                                      where
                                         rids = makeReverseIDMap ctx
                                         convert x = Map.findWithDefault "unknown" x rids
                                         matches = Set.filter match fact
                                         match (Predicate p a) = p == name && and (map (\(x,y) -> x == y) $ zip a args)
                                         lastArg (Predicate p a) = last a
                                         value = if Set.null matches then (-1) else lastArg $ (Set.toList matches)!!0


resolveVarsAbstract :: AbstractActionType a => Context -> Map.Map a a -> AbstractAction a -> AbstractAction a
resolveVarsAbstract ctx varmap (SuspectAction actor action) = SuspectAction actor $ resolveVarsAbstract ctx varmap action
resolveVarsAbstract ctx varmap (PublicArgument varname setname action) = PublicArgument varname setname $ resolveVarsAbstract ctx varmap action
resolveVarsAbstract ctx varmap (SecretArgument actors varname setname action) = SecretArgument (resolveList ctx varmap actors) varname setname $ resolveVarsAbstract ctx varmap action
resolveVarsAbstract ctx varmap (Inform actors action) = Inform (resolveList ctx varmap actors) $ resolveVarsPredicate varmap action
resolveVarsAbstract ctx varmap (Suspect actors action) = Suspect (resolveList ctx varmap actors) $ resolveVarsPredicate varmap action
resolveVarsAbstract ctx varmap (Sequence actions) = Sequence $ map (resolveVarsAbstract ctx varmap) actions
resolveVarsAbstract ctx varmap (OstariPrint s) = OstariPrint $ resolveList ctx (toStringMap ctx varmap) s
resolveVarsAbstract ctx varmap (Set term value) = Set (resolveVarsTerm varmap term) (resolveVarsTerm varmap value)
resolveVarsAbstract ctx varmap (Initialize term value) = Initialize (resolveVarsTerm varmap term) (resolveVarsTerm varmap value)
resolveVarsAbstract ctx varmap (UnSet term) = UnSet (resolveVarsTerm varmap term)
resolveVarsAbstract ctx varmap (If condition action) = If (resolveVarsPredicate varmap condition) $ resolveVarsAbstract ctx varmap action
resolveVarsAbstract ctx varmap (Precondition condition) = Precondition $ resolveVarsPredicate varmap condition
resolveVarsAbstract ctx varmap (IfElse condition ifaction elseaction) = IfElse (resolveVarsPredicate varmap condition) (resolveVarsAbstract ctx varmap ifaction) $ resolveVarsAbstract ctx varmap elseaction
resolveVarsAbstract ctx varmap (PublicIfElse actors condition ifaction elseaction) = PublicIfElse (resolveList ctx varmap actors) (resolveVarsPredicate varmap condition) (resolveVarsAbstract ctx varmap ifaction) $ resolveVarsAbstract ctx varmap elseaction
resolveVarsAbstract ctx varmap (Public actors inner) = Public (resolveList ctx varmap actors) $ resolveVarsAbstract ctx varmap inner
resolveVarsAbstract ctx varmap (DEL action) = DEL $ resolveVarsBaltag (toStringMap ctx varmap) action
resolveVarsAbstract ctx varmap (AddWeight w) = AddWeight w

resolveVarsPredicate :: AbstractActionType a =>  Map.Map a a -> Predicate a -> Predicate a
resolveVarsPredicate varmap (Forall var set pred) = Forall var set $ resolveVarsPredicate varmap pred
resolveVarsPredicate varmap (Each var set pred) = Each var set $ resolveVarsPredicate varmap pred
resolveVarsPredicate varmap (Which var set pred) = Which var set $ resolveVarsPredicate varmap pred
resolveVarsPredicate varmap (Exists var set pred) = Exists var set $ resolveVarsPredicate varmap pred
resolveVarsPredicate varmap (Equal t1 t2) = Equal (resolveVarsTerm varmap t1) $ resolveVarsTerm varmap t2
resolveVarsPredicate varmap (NotEqual t1 t2) = NotEqual (resolveVarsTerm varmap t1) $ resolveVarsTerm varmap t2
resolveVarsPredicate varmap (AndP t1 t2) = AndP (resolveVarsPredicate varmap t1) $ resolveVarsPredicate varmap t2
resolveVarsPredicate varmap (OrP t1 t2) = OrP (resolveVarsPredicate varmap t1) $ resolveVarsPredicate varmap t2
resolveVarsPredicate varmap (IsSet t1) = IsSet $ resolveVarsTerm varmap t1
resolveVarsPredicate varmap (IsUnSet t1) = IsUnSet $ resolveVarsTerm varmap t1
resolveVarsPredicate varmap (Believes a p) = Believes (Map.findWithDefault a a varmap) $ resolveVarsPredicate varmap p
resolveVarsPredicate varmap (StrongBelieves a p) = StrongBelieves (Map.findWithDefault a a varmap) $ resolveVarsPredicate varmap p
resolveVarsPredicate varmap (Probably op prob a p) = Probably op prob (Map.findWithDefault a a varmap) $ resolveVarsPredicate varmap p
resolveVarsPredicate varmap (WeightedProbably w op prob a p) = WeightedProbably w op prob (Map.findWithDefault a a varmap) $ resolveVarsPredicate varmap p
resolveVarsPredicate varmap (NotBelieves a p) = NotBelieves (Map.findWithDefault a a varmap) $ resolveVarsPredicate varmap p

resolveVarsTerm :: AbstractActionType a => Map.Map a a -> Term a -> Term a
resolveVarsTerm varmap (Variable name) | Map.member name varmap = Constant $ Map.findWithDefault name name varmap
                                       | otherwise              = Variable name
resolveVarsTerm varmap (Property name arg) = Property name $ resolveVarsTerm varmap arg
resolveVarsTerm varmap (Property2 name arg1 arg2) = Property2 name (resolveVarsTerm varmap arg1) $ resolveVarsTerm varmap arg2
resolveVarsTerm varmap (PropertyN name args) = PropertyN name $ map (resolveVarsTerm varmap) args
resolveVarsTerm varmap (Constant value) = Constant value
resolveVarsTerm varmap (IndexedProperty name arg) = IndexedProperty name $ resolveVarsTerm varmap arg

resolveList :: AbstractActionType a => Context -> Map.Map a a -> [a] -> [a]
resolveList ctx vars items | (length items == 1) && (Map.member (head items) (getSets ctx)) = Map.findWithDefault [] (head items) $ getSets ctx
                           | otherwise = map (\x -> Map.findWithDefault x x vars) items
                           
splitAction :: Context -> AbstractAction a -> ([(a,[a],a)], AbstractAction a)
splitAction ctx (SuspectAction actor action) = splitAction ctx action
splitAction ctx (PublicArgument varname setname action) = ((varname, [], setname):sub,subaction)
                                                       where
                                                          (sub,subaction) = splitAction ctx action
splitAction ctx (SecretArgument actors varname setname action) = ((varname, actors, setname):sub,subaction)
                                                       where
                                                          (sub,subaction) = splitAction ctx action
splitAction ctx action = ([],action)

                           
optimizeAction :: Context -> AbstractAction String -> AbstractAction Int
optimizeAction ctx (SuspectAction actor action) = SuspectAction (strToInt ctx actor) $ optimizeAction ctx action
optimizeAction ctx (PublicArgument varname setname action) = PublicArgument (strToInt ctx varname) (strToInt ctx setname) $ optimizeAction ctx action
optimizeAction ctx (SecretArgument actors varname setname action) = SecretArgument (map (strToInt ctx) actors) (strToInt ctx varname) (strToInt ctx setname) $ optimizeAction ctx action
optimizeAction ctx (Inform actors action) = Inform (map (strToInt ctx) actors) $ optimizePredicate ctx action
optimizeAction ctx (Suspect actors action) = Suspect (map (strToInt ctx) actors) $ optimizePredicate ctx action
optimizeAction ctx (Sequence actions) = Sequence $ map (optimizeAction ctx) actions
optimizeAction ctx (Set term value) = Set (optimizeTerm ctx  term) (optimizeTerm ctx value)
optimizeAction ctx (Initialize term value) = Initialize (optimizeTerm ctx  term) (optimizeTerm ctx value)
optimizeAction ctx (UnSet term) = UnSet (optimizeTerm ctx  term)
optimizeAction ctx (If condition action) = If (optimizePredicate ctx  condition) $ optimizeAction ctx action
optimizeAction ctx (Precondition condition) = Precondition $ optimizePredicate ctx  condition
optimizeAction ctx (IfElse condition ifaction elseaction) = IfElse (optimizePredicate ctx condition) (optimizeAction ctx ifaction) $ optimizeAction ctx elseaction
optimizeAction ctx (PublicIfElse actors condition ifaction elseaction) = PublicIfElse (map (strToInt ctx) actors) (optimizePredicate ctx condition) (optimizeAction ctx ifaction) $ optimizeAction ctx  elseaction
optimizeAction ctx (Public actors inner) = Public (map (strToInt ctx) actors) $ optimizeAction ctx inner
optimizeAction ctx (DEL action) = DEL action
optimizeAction ctx (AddWeight w) = AddWeight w
optimizeAction ctx (OstariPrint s) = OstariPrint s

optimizePredicate :: Context -> Predicate String -> Predicate Int
optimizePredicate ctx (Forall var set pred) = Forall (strToInt ctx var) (strToInt ctx set) $ optimizePredicate ctx pred
optimizePredicate ctx (Each var set pred) = Each (strToInt ctx var) (strToInt ctx set) $ optimizePredicate ctx pred
optimizePredicate ctx (Which var set pred) = Which (strToInt ctx var) (strToInt ctx set) $ optimizePredicate ctx pred
optimizePredicate ctx (Exists var set pred) = Exists (strToInt ctx var) (strToInt ctx set) $ optimizePredicate ctx pred
optimizePredicate ctx (Equal t1 t2) = Equal (optimizeTerm ctx t1) $ optimizeTerm ctx t2
optimizePredicate ctx (NotEqual t1 t2) = NotEqual (optimizeTerm ctx t1) $ optimizeTerm ctx t2
optimizePredicate ctx (AndP t1 t2) = AndP (optimizePredicate ctx t1) $ optimizePredicate ctx t2
optimizePredicate ctx (OrP t1 t2) = OrP (optimizePredicate ctx t1) $ optimizePredicate ctx t2
optimizePredicate ctx (IsSet t1) = IsSet $ optimizeTerm ctx t1
optimizePredicate ctx (IsUnSet t1) = IsUnSet $ optimizeTerm ctx t1
optimizePredicate ctx (Believes a p) = Believes (strToInt ctx a) $ optimizePredicate ctx p
optimizePredicate ctx (StrongBelieves a p) = StrongBelieves (strToInt ctx a) $ optimizePredicate ctx p
optimizePredicate ctx (Probably op prob a p) = Probably op prob (strToInt ctx a) $ optimizePredicate ctx p
optimizePredicate ctx (WeightedProbably w op prob a p) = WeightedProbably (strToInt ctx w) op prob (strToInt ctx a) $ optimizePredicate ctx p
optimizePredicate ctx (NotBelieves a p) = NotBelieves (strToInt ctx a) $ optimizePredicate ctx p

optimizeTerm :: Context -> Term String -> Term Int
optimizeTerm ctx (Variable name) = Variable $ strToInt ctx name
optimizeTerm ctx (Property name arg) = Property (strToInt ctx name) $ optimizeTerm ctx arg
optimizeTerm ctx (Property2 name arg1 arg2) = Property2 (strToInt ctx name) (optimizeTerm ctx arg1) $ optimizeTerm ctx arg2
optimizeTerm ctx (PropertyN name args) = PropertyN (strToInt ctx name) $ map (optimizeTerm ctx) args
optimizeTerm ctx (Constant value) = Constant $ strToInt ctx value
optimizeTerm ctx (IndexedProperty name arg) = IndexedProperty name $ optimizeTerm ctx arg

