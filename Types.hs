{-# LANGUAGE GADTs, NamedFieldPuns, FlexibleInstances, MultiParamTypeClasses, InstanceSigs #-}

module Types where

import Control.Monad (replicateM)
import Data.Bifunctor (second)
import Data.List (delete, intercalate, (\\))
import Data.Maybe (fromMaybe)
import Prelude hiding (id)

type Identifier  = String
type Constructor = String
type TypeVar     = String

data Term where
    Var   :: Identifier -> Term
    Data  :: Constructor -> [Term] -> Term
    App   :: Term -> Term -> Term
    Abs   :: Identifier -> Identifier -> Term -> Term
    Match :: Term -> [Matching] -> Term
    deriving (Eq)

type Matching = (Pattern, Term)
type Pattern = (Constructor, [Identifier])

data Type where
    Ok       :: Type
    TypeVar  :: TypeVar -> Type
    DataType :: Constructor -> [Type] -> Type
    SufArrow :: Type -> Type -> Type
    NecArrow :: Type -> Type -> Type
    deriving (Eq)

data TypeScheme
    = Mono Type
    | Poly [TypeVar] ConstraintSet Type
    deriving (Eq)

type ConstraintSet = [Constraint]  -- Use Set eventually
type Constraint    = (Type, Type)

isValue :: Term -> Bool
isValue (Var{})  = True
isValue (Data{}) = True
isValue _        = False

type Env = [(Term, TypeScheme)]

toType :: TypeScheme -> Type
toType (Mono t)     = t
toType (Poly _ _ t) = t

data Judgement = Judgement { left :: Env, right :: Env }
    deriving (Eq)

type Subst a = [(Identifier, a)]

class HasVariables a b where
    apply :: Subst b -> a -> a
    applyMany :: [Subst b] -> a -> a
    applyMany subs t = foldr apply t subs

class HasTermVariables a where
    fv :: a -> [Identifier]

emptySubst :: Subst a
emptySubst = []

mkSubst :: Identifier -> a -> Subst a
mkSubst x t = [(x, t)]

mkSubsts :: [Identifier] -> [a] -> [Subst a]
mkSubsts [] [] = []
mkSubsts (x : xs) (t : ts) = mkSubst x t : mkSubsts xs ts
mkSubsts _ _ = error "mkSubsts.different-lengths"

removeSub :: Identifier -> Subst a -> Subst a
removeSub x = filter (\sub -> fst sub /= x)

removeSub2 :: Identifier -> Identifier -> Subst a -> Subst a
removeSub2 x y = removeSub x <$> removeSub y

instance HasVariables Term Term where
    apply :: Subst Term -> Term -> Term
    apply s (Var x) = fromMaybe (Var x) (lookup x s)
    apply s t@(Abs f x m) = Abs f x (apply s' m)
      where
        s' = removeSub2 f x s
    apply s (App m n) = App (apply s m) (apply s n)
    apply s (Data name fields) = Data name (map (apply s) fields)
    apply s (Match m matches) = Match (apply s m) matches' -- bound vars!!!
      where
        matches' = map (second (apply s)) matches

instance HasTermVariables Term where
    fv :: Term -> [Identifier]
    fv (Var x) = [x]
    fv (Data _ fields) = concatMap fv fields
    fv (App m n) = fv m ++ fv n
    fv (Abs f x m) = delete f (delete x (fv m))
    fv (Match m matches) = (fv m ++ freeVars) \\ boundVars
      where
        (boundVars, freeVars) =
            foldr
                (\(a, b) (c, d) -> (fv a ++ c, fv b ++ d))
                ([], [])
                matches

instance HasTermVariables Matching where
    fv :: Matching -> [Identifier]
    fv (_, t) = fv t

instance HasTermVariables Pattern where
    fv :: Pattern -> [Identifier]
    fv = snd

instance HasVariables Type Type where
    apply :: Subst Type -> Type -> Type
    apply s Ok = Ok
    apply s (TypeVar x) = fromMaybe (TypeVar x) (lookup x s)
    apply s (DataType c fields) = DataType c (apply s fields)
    apply s (SufArrow a b) = SufArrow (apply s a) (apply s b)
    apply s (NecArrow a b) = NecArrow (apply s a) (apply s b)

instance (HasVariables a b) => HasVariables [a] b where
    apply :: Subst b -> [a] -> [a]
    apply s [] = []
    apply s (t : ts) = apply s t : apply s ts

instance HasVariables Constraint Type where
    apply :: Subst Type -> Constraint -> Constraint
    apply s (a, b) = (apply s a, apply s b)

instance Show Judgement where
    show :: Judgement -> String
    show Judgement{left, right} = show left ++ " ⊢ " ++ show right

instance {-# OVERLAPPING #-} Show Constraint where
    show :: Constraint -> String
    show (a, b) = show a ++ " ⊑ " ++ show b

instance {-# OVERLAPPING #-} Show ConstraintSet where
    show :: ConstraintSet -> String
    show [] = ""
    show (x : xs) = show x ++ ", " ++ show xs

instance {-# OVERLAPPING #-} Show (Term, TypeScheme) where
    show :: (Term, TypeScheme) -> String
    show (term, ty) = show term ++ " : " ++ show ty

instance {-# OVERLAPPING #-} Show Env where
    show :: Env -> String
    show = intercalate ", " . map show

instance Show Type where
    show :: Type -> String
    show Ok = "OK"
    show (TypeVar uid) = "'" ++ varNames !! read uid
    show (DataType c []) = c
    show (DataType c fields) = c ++ "(" ++ show fields ++ ")"
    show (SufArrow a b) = "(" ++ show a ++ " → " ++ show b ++ show ")"
    show (NecArrow a b) = "(" ++ show a ++ " ⤚ " ++ show b ++ show ")"

varNames :: [String]
varNames = [1..] >>= flip replicateM ['a' .. 'z']

instance Show TypeScheme where
    show :: TypeScheme -> String
    show (Mono t) = show t
    show (Poly vars rels t) = "∀" ++ concatMap ((varNames !!) . read) vars ++ show rels ++ "." ++ show t

instance Show Term where
    show :: Term -> String
    show (Var x) = x
    show (Data c fields) = c ++ "(" ++ show fields ++ ")"
    show (App m n) = "(" ++ show m ++ " " ++ show n ++ ")"
    show (Abs f x m) = f ++ "(\\" ++ x ++ ". " ++ show m ++ ")"
    show (Match m pats) = "match " ++ show m ++ " with " ++ show pats