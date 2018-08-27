{-# LANGUAGE FlexibleInstances #-}
module Baltag where

import BaseTypes
import Data.List
import qualified Data.Map as Map
import qualified Data.Set as Set
import Debug.Trace

data BaltagProperty a = BaltagPropertyN a [BaltagProperty a] | Value a
                      deriving (Read, Show, Eq)

data Proposition a = Atom (AtProp a)
                 | Not (Proposition a)
                 | Or (Proposition a) (Proposition a)
                 | And (Proposition a) (Proposition a)
                 | Apply (Action a) (Proposition a)
                 | Know Actor (Proposition a)
                 | StrongKnow Actor (Proposition a)
                 | ProbablyKnow Op Float Actor (Proposition a)
                 | MutualKnowledge [Actor] (Proposition a)
                 | PropertyEquality (BaltagProperty a) (BaltagProperty a)
                 | PropertyInequality (BaltagProperty a) (BaltagProperty a)
                 deriving (Read, Show, Eq)

data Action a = Flip (AtProp a)
            | Test (Proposition a)
            | Print [String]
            | Choice (Action a) (Action a)
            | Composition (Action a) (Action a)
            | Learn (Action a) Actor
            | MutualLearn (Action a) [Actor]
              deriving (Read, Show, Eq)

class (Eq a, Ord a, Show a) => ActionType a where
    true :: Proposition a
    false :: Proposition a
    false = Not true
    testtrue :: Action a
    testtrue = Test true
    testfalse :: Action a
    testfalse = Test false
    skip :: Action a
    skip = testtrue

instance ActionType Int where
    true = Atom $ Predicate 0 []

instance ActionType String where
    true = Atom $ Predicate "true" []

termCount :: ActionType a => Action a -> Int
termCount (Flip _) = 1
termCount (Test _) = 1
termCount (Print _) = 0
termCount (Choice a b) = (termCount a) + (termCount b)
termCount (Composition a b) = (termCount a) + (termCount b)
termCount (Learn a _) = termCount a
termCount (MutualLearn a _) = termCount a


sumAction :: ActionType a => [Action a] -> Action a
sumAction [] = testfalse
sumAction actions = foldr1 Choice $ actions



cleanChoice :: ActionType a => Action a -> Action a -> Action a
cleanChoice a b | a == testtrue = testtrue
                | b == testtrue = testtrue
                | a == testfalse = b
                | b == testfalse = a
                | otherwise = Choice a b

cleanSum :: ActionType a => [Action a] -> Action a
cleanSum [] = testfalse
cleanSum actions = foldr1 cleanChoice $ nub actions



productAction :: ActionType a => [Action a] -> Action a
productAction [] = skip
productAction actions = foldr1 Composition $ nub actions

cleanComposition :: ActionType a => Action a -> Action a -> Action a
cleanComposition a b | a == testtrue = b
                     | b == testtrue = a
                     | a == testfalse = testfalse
                     | b == testfalse = testfalse
                     | otherwise = Composition a b

cleanProduct :: ActionType a => [Action a] -> Action a
cleanProduct [] = skip
cleanProduct actions = foldr1 cleanComposition $ nub actions


cleanAnd :: ActionType a => Proposition a -> Proposition a -> Proposition a
cleanAnd a b | a == false = false
             | b == false = false
             | a == true = b
             | b == true = a
             | otherwise = And a b
             

cleanOr :: ActionType a => Proposition a -> Proposition a -> Proposition a
cleanOr a b | a == false = b
            | b == false = a
            | a == true = true
            | b == true = true
            | otherwise = Or a b

pre :: ActionType a => Action a -> Proposition a
pre (Test prop) = prop
pre (Choice a b) = cleanOr (pre a) (pre b)
pre (Composition a b) | hasChange a = cleanAnd (pre a) (Apply a (pre b))
                      | otherwise   = And (pre a) (pre b)
pre (MutualLearn act _) = pre act
pre _ = true

hasChange :: ActionType a => Action a -> Bool
hasChange (Test prop) = False
hasChange (Print _) = False
hasChange (Choice a b) = (hasChange a) || (hasChange b)
hasChange (Composition a b) = (hasChange a) || (hasChange b)
hasChange (MutualLearn act _) = hasChange act
hasChange _ = True

appearance :: ActionType a =>  Actor -> Action a -> Action a
appearance a (Learn act who) | who == a  = act
                             | otherwise = skip
appearance a (Choice act1 act2) = cleanChoice (appearance a act1) (appearance a act2)
appearance a (Composition act1 act2) = cleanComposition (appearance a act1) (appearance a act2)
appearance a (MutualLearn act actors) | a `elem` actors = cleanComposition (appearance a act) (MutualLearn act actors)
                                      | otherwise = appearance a act
appearance _ _ = skip

issimple :: ActionType a => Action a -> Bool
issimple (Flip _) = True
issimple (Test _) = True
issimple (Print _) = True
issimple (Composition a b) = (issimple a) && (issimple b)
issimple (Learn _ _) = True
issimple (MutualLearn act _) = issimple act
issimple _ = False



content :: ActionType a => Action a -> Set.Set (AtProp a)
content (Flip p) = Set.singleton p
content (Test _) = Set.empty
content (Print _) = Set.empty
content (Composition a b) = symdiff (content a) (content b)
content (Learn _ _) = Set.empty
content (MutualLearn act _) = content act
content _ = Set.empty

output :: ActionType a => Action a -> String
output (Print s) = "> " ++ (intercalate " " $ map toOutput s) ++ "\n"
output (Composition a b) = (output a) ++ (output b)
output (MutualLearn act _) = output act
output _ = ""



choice :: ActionType a => Action a -> [Action a]
choice act | issimple act = [act]
           | otherwise = choice' act
           
choice' :: ActionType a => Action a -> [Action a]
choice' (Choice a b)             = (choice a) `union` (choice b)
choice' (Composition a b)        = [Composition a1 b1 | a1 <- (choice a), b1 <- (choice b)]
choice' (MutualLearn act actors) = [Composition a subaction | a <- (choice act)]
                                 where 
                                    subaction = productAction [Learn (MutualLearn act actors) a | a <- actors]
choice' _ = []

alternatives :: ActionType a => Actor -> Action a -> [Action a]
alternatives a act = choice $ appearance a act
    
data PointedModel = PM (Map.Map String [PointedModel]) (Set.Set (AtProp Int)) [String] Context (Map.Map [Int] (Set.Set Int))

instance Show PointedModel where
    show (PM app props acts _ _) = intercalate ", " $ map (show) $ Set.toList props
 
truth :: Maybe PointedModel -> [AtProp Int]
truth (Just (PM app fact _ _ _)) = Set.toList fact
truth Nothing = []

fact (PM app f _ _ _) = f

appearanceB (PM app _ _ _ _) = app

factList (PM app f _ _ _) = Set.toList f

looksLike :: PointedModel -> String -> [PointedModel]
looksLike (PM app _ _ _ _) act = Map.findWithDefault [] act app

getAtPropArgs :: AtProp a -> [a]
getAtPropArgs (Predicate name args) = args

propertyValueB :: (Set.Set (AtProp Int)) -> Context -> BaltagProperty Int -> Int
propertyValueB facts ctx (Value a) = a
propertyValueB facts ctx (BaltagPropertyN name args) = result 
                                                where
                                                    ground =  map (propertyValueB facts ctx) args
                                                    sigs = signaturesi ctx
                                                    s = setsi ctx
                                                    types = Map.findWithDefault [-1] name sigs
                                                    values = Map.findWithDefault [] (head types) s
                                                    matches = filter (\v -> Set.member (Predicate name (ground ++ [v])) facts) values
                                                    result = if null matches then (-1) else head matches


type IDMap = Map.Map Int String

class PrettyPrint a where
    toString :: IDMap -> a -> String
    toLaTeX :: IDMap -> a -> String
    
instance PrettyPrint PointedModel where
    toLaTeX _ _ = ""
    toString ids (PM app f actors _ _) = "Truth: " ++ (show $ Set.toList $ Set.map (toString ids) f) ++ " looks like: \n" ++ (intercalate "" $ map (\act -> (act ++ ": " ++ (show $ map (map (toString ids)) $ map factList $ Map.findWithDefault [] act app) ++ "\n")) actors)
    
instance PrettyPrint (AtProp Int) where
    toString ids (Predicate name args) = (Map.findWithDefault "unknown" name ids) ++ "(" ++ (intercalate "," $ map (\a -> Map.findWithDefault "unknown" a ids) args) ++ ")"
    toLaTeX ids (Predicate name args) = (Map.findWithDefault "unknown" name ids) ++ "\\left(" ++ (intercalate "," $ map (\a -> Map.findWithDefault "unknown" a ids) args) ++ "\\right)"
    
formatOp AtMost = "<"
formatOp AtLeast = ">"

    
instance PrettyPrint (Proposition Int) where
    toString ids (Atom prop) = toString ids prop
    toString ids (Not prop) = "!" ++ (toString ids prop)
    toString ids (And p1 p2) = "(" ++ (toString ids p1) ++ " ^ " ++ (toString ids p2) ++ ")"
    toString ids (Or p1 p2) = "(" ++ (toString ids p1) ++ " v " ++ (toString ids p2) ++ ")"
    toString ids (Apply act prop) = "[" ++ (toString ids act) ++ "]" ++ (toString ids prop)
    toString ids (Know act prop) = "B_" ++ act ++ " " ++ (toString ids prop)
    toString ids (StrongKnow act prop) = "B!_" ++ act ++ " " ++ (toString ids prop)
    toString ids (ProbablyKnow op p act prop) = "P[" ++ (formatOp op) ++ (show p) ++ "]_" ++ act ++ " " ++ (toString ids prop)
    toString ids (MutualKnowledge acts prop) = "B*_" ++ (intercalate "," acts) ++ " " ++ (toString ids prop)
    toString ids (PropertyEquality a b) = (toString ids a) ++ " == " ++ (toString ids b)
    
    toLaTeX ids (Atom prop) = toLaTeX ids prop
    toLaTeX ids (Not prop) = "\\neg" ++ (toLaTeX ids prop)
    toLaTeX ids (And p1 p2)= "\\left(" ++ (toLaTeX ids p1) ++ " \\wedge {" ++ (toLaTeX ids p2) ++ "}\\right)"
    toLaTeX ids (Or p1 p2)= "\\left(" ++ (toLaTeX ids p1) ++ " \\vee {" ++ (toLaTeX ids p2) ++ "}\\right)"
    toLaTeX ids (Apply act prop) = "\\left[" ++ (toLaTeX ids act) ++ "\right]" ++ (toLaTeX ids prop)
    toLaTeX ids (Know act prop) = "B_{" ++ act ++ "} " ++ (toLaTeX ids prop)
    toLaTeX ids (MutualKnowledge acts prop) = "B*_{" ++ (intercalate "," acts) ++ "} " ++ (toLaTeX ids prop)
    
instance PrettyPrint (Action Int) where
    toString ids (Flip prop) = "flip " ++ (toString ids prop)
    toString ids (Test prop) = "?" ++ (toString ids prop)
    toString ids (Choice a1 a2) = (toString ids a1) ++ " + " ++ (toString ids a2)
    toString ids (Composition (Choice a1 a2) (Choice b1 b2)) = "(" ++ (toString ids (Choice a1 a2)) ++ ") . (" ++ (toString ids (Choice b1 b2)) ++ ")"
    toString ids (Composition (Choice a1 a2) b) = "(" ++ (toString ids (Choice a1 a2)) ++ ") . " ++ (toString ids b)
    toString ids (Composition a (Choice b1 b2)) = (toString ids a) ++ " . (" ++ (toString ids (Choice b1 b2)) ++ ")"
    toString ids (Composition a1 a2) = (toString ids a1) ++ " . " ++ (toString ids a2)
    toString ids (Learn act actor) = "(" ++ (toString ids act) ++ ")^" ++ actor
    toString ids (Print s) = "Print(" ++ (intercalate ", " s) ++")"
    toString ids (MutualLearn act actors) = "(" ++ (toString ids act) ++ ")*^" ++ (intercalate "," actors) 
    
    toLaTeX ids (Flip prop) = "\\text{flip} " ++ (toLaTeX ids prop)
    toLaTeX ids (Test prop) = "\\?" ++ (toLaTeX ids prop)
    toLaTeX ids (Choice a1 a2) = "\\left(" ++ (toLaTeX ids a1) ++ " + " ++ (toLaTeX ids a2) ++ "\\right)"
    toLaTeX ids (Composition a1 a2) = "\\left(" ++ (toLaTeX ids a1) ++ " \\cdot " ++ (toLaTeX ids a2) ++ "\\right)"
    toLaTeX ids (Learn act actor) = "\\left(" ++ (toLaTeX ids act) ++ "\\right)^{" ++ actor ++ "}"
    toLaTeX ids (MutualLearn act actors) = "\\left(" ++ (toLaTeX ids act) ++ "\\right)*^{" ++ (intercalate "," actors) ++ "}"
    
instance PrettyPrint (BaltagProperty Int) where
    toString ids (BaltagPropertyN name args) = (Map.findWithDefault "unknown" name ids) ++ "(" ++ (intercalate ", " $ map (toString ids) args) ++ ")"
    toString ids (Value val) = Map.findWithDefault "unknown" val ids
    
    toLaTeX ids _ = "not implemented"
    
