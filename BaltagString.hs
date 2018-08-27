{-# LANGUAGE FlexibleInstances #-}
module BaltagString where

import Baltag
import BaseTypes
import Data.List
import qualified Data.Map as Map

optimize :: Map.Map String Int -> Action String -> Action Int
optimize ids (Flip p) = Flip $ optimizeAtProp ids p
optimize ids (Test p) = Test $ optimizeProposition ids p
optimize ids (Print s) = Print s
optimize ids (Choice a b) = Choice (optimize ids a) (optimize ids b)
optimize ids (Composition a b) = Composition (optimize ids a) (optimize ids b)
optimize ids (Learn a actor) = Learn (optimize ids a) actor
optimize ids (MutualLearn a actors) = MutualLearn (optimize ids a) actors

optimizeProposition :: Map.Map String Int -> Proposition String -> Proposition Int
optimizeProposition ids (Atom atom) = Atom $ optimizeAtProp ids atom
optimizeProposition ids (Not p) = Not $ optimizeProposition ids p
optimizeProposition ids (Or a b) = Or (optimizeProposition ids a) $ optimizeProposition ids b
optimizeProposition ids (And a b) = And (optimizeProposition ids a) $ optimizeProposition ids b
optimizeProposition ids (Know act a) = Know act $ optimizeProposition ids a
optimizeProposition ids (StrongKnow act a) = StrongKnow act $ optimizeProposition ids a
optimizeProposition ids (ProbablyKnow op p act a) = ProbablyKnow op p act $ optimizeProposition ids a
optimizeProposition ids (MutualKnowledge act a) = MutualKnowledge act $ optimizeProposition ids a
optimizeProposition ids (PropertyEquality a b) = PropertyEquality (optimizeProperty ids a) $ optimizeProperty ids b
optimizeProposition ids (PropertyInequality a b) = PropertyInequality (optimizeProperty ids a) $ optimizeProperty ids b

optimizeProperty ids (Value a) = Value (Map.findWithDefault (-1) a ids)
optimizeProperty ids (BaltagPropertyN name args) = BaltagPropertyN (Map.findWithDefault (-1) name ids) $ map (optimizeProperty ids) args


optimizeAtProp :: Map.Map String Int -> AtProp String -> AtProp Int
optimizeAtProp _ (Predicate "true" []) = (Predicate 0 [])
optimizeAtProp ids (Predicate name args) = Predicate (Map.findWithDefault (-1) name ids) $ map (\a -> Map.findWithDefault (-1) a ids) args


resolveVarsBaltag :: Map.Map String String -> Action String -> Action String
resolveVarsBaltag varmap (Flip at) = Flip $ resolveVarsAtom varmap at
resolveVarsBaltag varmap (Test prop) = Test $ resolveVarsProposition varmap prop
resolveVarsBaltag varmap (Print s) = Print $ resolveVarsString varmap s
resolveVarsBaltag varmap (Choice a b) = Choice (resolveVarsBaltag varmap a) $ resolveVarsBaltag varmap b
resolveVarsBaltag varmap (Composition a b) = Composition (resolveVarsBaltag varmap a) $ resolveVarsBaltag varmap b
resolveVarsBaltag varmap (Learn action actor) = Learn (resolveVarsBaltag varmap action) $ resolveVarsItem varmap actor
resolveVarsBaltag varmap (MutualLearn action actors) = MutualLearn (resolveVarsBaltag varmap action) $ map (resolveVarsItem varmap) actors

resolveVarsString varmap xs = map (\x -> Map.findWithDefault x x varmap) xs

resolveVarsProposition :: Map.Map String String -> Proposition String -> Proposition String
resolveVarsProposition varmap (Atom at) = Atom $ resolveVarsAtom varmap at
resolveVarsProposition varmap (Not p) = Not $ resolveVarsProposition varmap p
resolveVarsProposition varmap (Or a b) = Or (resolveVarsProposition varmap a) $ resolveVarsProposition varmap b
resolveVarsProposition varmap (And a b) = And (resolveVarsProposition varmap a) $ resolveVarsProposition varmap b
resolveVarsProposition varmap (Know actor prop) = Know (resolveVarsItem varmap actor) $ resolveVarsProposition varmap prop
resolveVarsProposition varmap (StrongKnow actor prop) = StrongKnow (resolveVarsItem varmap actor) $ resolveVarsProposition varmap prop
resolveVarsProposition varmap (ProbablyKnow op p actor prop) = ProbablyKnow op p (resolveVarsItem varmap actor) $ resolveVarsProposition varmap prop
resolveVarsProposition varmap (MutualKnowledge actors prop) = MutualKnowledge (map (resolveVarsItem varmap) actors) $ resolveVarsProposition varmap prop
resolveVarsProposition varmap a = a


resolveVarsAtom :: Map.Map String String -> AtProp String -> AtProp String
resolveVarsAtom varmap (Predicate a args) = Predicate (resolveVarsItem varmap a) $ map (resolveVarsItem varmap) args

resolveVarsItem :: Map.Map String String -> String -> String
resolveVarsItem varmap a = Map.findWithDefault a a varmap
            
instance PrettyPrint (AtProp String) where
    toString ids (Predicate name args) = name ++ "(" ++ (intercalate ","  args) ++ ")"
    toLaTeX ids (Predicate name args) = name ++ "\\left(" ++ (intercalate "," args) ++ "\\right)"
            
instance PrettyPrint (Proposition String) where
    toString ids (Atom prop) = toString ids prop
    toString ids (Not prop) = "!" ++ (toString ids prop)
    toString ids (And p1 p2) = "(" ++ (toString ids p1) ++ " ^ " ++ (toString ids p2) ++ ")"
    toString ids (Apply act prop) = "[" ++ (toString ids act) ++ "]" ++ (toString ids prop)
    toString ids (Know act prop) = "B_" ++ act ++ " " ++ (toString ids prop)
    toString ids (MutualKnowledge acts prop) = "B*_" ++ (intercalate "," acts) ++ " " ++ (toString ids prop)
    
    toLaTeX ids (Atom prop) = toLaTeX ids prop
    toLaTeX ids (Not prop) = "\\neg" ++ (toLaTeX ids prop)
    toLaTeX ids (And p1 p2)= "\\left(" ++ (toLaTeX ids p1) ++ " ^ {" ++ (toLaTeX ids p2) ++ "}\\right)"
    toLaTeX ids (Apply act prop) = "\\left[" ++ (toLaTeX ids act) ++ "\right]" ++ (toLaTeX ids prop)
    toLaTeX ids (Know act prop) = "B_{" ++ act ++ "} " ++ (toLaTeX ids prop)
    toLaTeX ids (MutualKnowledge acts prop) = "B*_{" ++ (intercalate "," acts) ++ "} " ++ (toLaTeX ids prop)
    
instance PrettyPrint (Action String) where
    toString ids (Flip prop) = "flip " ++ (toString ids prop)
    toString ids (Test prop) = "?" ++ (toString ids prop)
    toString ids (Choice a1 a2) = (toString ids a1) ++ " + " ++ (toString ids a2)
    toString ids (Composition (Choice a1 a2) (Choice b1 b2)) = "(" ++ (toString ids (Choice a1 a2)) ++ ") . (" ++ (toString ids (Choice b1 b2)) ++ ")"
    toString ids (Composition (Choice a1 a2) b) = "(" ++ (toString ids (Choice a1 a2)) ++ ") . " ++ (toString ids b)
    toString ids (Composition a (Choice b1 b2)) = (toString ids a) ++ " . (" ++ (toString ids (Choice b1 b2)) ++ ")"
    toString ids (Composition a1 a2) = (toString ids a1) ++ " . " ++ (toString ids a2)
    toString ids (Learn act actor) = "(" ++ (toString ids act) ++ ")^" ++ actor
    toString ids (MutualLearn act actors) = "(" ++ (toString ids act) ++ ")*^" ++ (intercalate "," actors) 
    
    toLaTeX ids (Flip prop) = "\\text{flip} " ++ (toLaTeX ids prop)
    toLaTeX ids (Test prop) = "\\?" ++ (toLaTeX ids prop)
    toLaTeX ids (Choice a1 a2) = "\\left(" ++ (toLaTeX ids a1) ++ " + " ++ (toLaTeX ids a2) ++ "\\right)"
    toLaTeX ids (Composition a1 a2) = "\\left(" ++ (toLaTeX ids a1) ++ " \\cdot " ++ (toLaTeX ids a2) ++ "\\right)"
    toLaTeX ids (Learn act actor) = "\\left(" ++ (toLaTeX ids act) ++ "\\right)^{" ++ actor ++ "}"
    toLaTeX ids (MutualLearn act actors) = "\\left(" ++ (toLaTeX ids act) ++ "\\right)*^{" ++ (intercalate "," actors) ++ "}"