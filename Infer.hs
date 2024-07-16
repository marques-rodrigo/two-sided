{-# OPTIONS_GHC -Wno-unrecognised-pragmas #-}
{-# HLINT ignore "Redundant $" #-}
module Infer where

import Control.Applicative
import Control.Monad.List
import Control.Monad.State.Strict
import Data.List
import Data.Maybe
import Debug.Trace (traceM)
import Types
import Prelude hiding (succ)
import Data.Bifunctor

verbose :: Bool
verbose = False


type Infer a = StateT InferState [] a
data InferState = InferState {count :: Int, constraints :: ConstraintSet}
    deriving (Eq)

initInferState :: InferState
initInferState = InferState {count = 0, constraints = []}

inferR :: Env -> Term -> Infer Type
inferR left term = do
    case term of
        Var x -> do
            b <- freshVar
            case lookup term left of
                Nothing -> do
                    constrain Ok b
                    return b
                Just (Mono t) -> do
                    constrain t b
                    return b
                Just (Poly vars rels t) -> do
                    bs <- sequence [freshVar | _ <- vars]
                    let subs = mkSubsts vars bs
                        instType = applyMany subs t
                        instRels = applyMany subs rels
                    constrain instType b
                    mapM_ (uncurry constrain) instRels
                    return b
        App m n -> do
            res <- freshVar
            fun <- inferR left m
            arg <- inferR left n
            constrain fun (SufArrow arg res)
            return res
        Abs f x body -> inferNecessity <|> inferSufficiency
          where
            inferSufficiency = do
                fun <- freshVar
                arg <- freshVar
                let left = (Var x, Mono arg) : if f /= "" then (Var f, Mono fun) : left else left
                res <- inferR left body
                constrain (SufArrow arg res) fun
                return fun
            inferNecessity = do
                fun <- freshVar
                arg <- freshVar
                let left = (Var x, Mono arg) : if f /= "" then (Var f, Mono fun) : left else left
                res <- inferL left body [(Var x, Mono arg)]
                constrain (NecArrow arg res) fun
                return fun
        Data name fields -> do
            a <- freshVar
            fieldTypes <- mapM (inferR left) fields
            constrain (DataType name fieldTypes) a
            return a
        Match m matches -> do
            res <- freshVar
            matchedType <- inferR left m
            forM_ matches (\((name, vars), body) -> do
                bs <- sequence [freshVar | _ <- vars]
                let subs = zip vars bs
                    typs = map (bimap Var Mono) subs
                bodyType <- inferR (typs ++ left) body
                let patternType = apply subs (DataType name (map TypeVar vars))
                constrain bodyType res
                constrain matchedType patternType)
            return res

inferL :: Env -> Term -> Env -> Infer Type
inferL left term right = do
    case right of
        [(Var x, b)] -> do
            a <- freshVar
            constrain Ok (toType b)
            return a
        _ -> fail ""
    <|> inferL' left term right

inferL' :: Env -> Term -> Env -> Infer Type
inferL' left term right = case term of
    Var x -> do
        case lookup term right of
            Nothing -> fail "Lookup fail on the right"
            Just b -> do
                a <- freshVar
                constrain a (toType b)
                return a
    App m n -> infer1 <|> infer2
      where
        infer1 = do
            res <- freshVar
            fun <- inferR left m
            arg <- inferL left n right
            constrain fun (NecArrow arg res)
            return res
        infer2 = do
            res <- freshVar
            fun <- inferL left m right
            constrain (NecArrow Ok res) fun
            return res
    Abs _ x m -> do
        a <- freshVar
        constrain a (DataType "DATATYPE" []) 
        return a
    Data name fields -> infer1 <|> infer2 <|> infer3 <|> infer4 <|> infer5
      where
        infer1 = do
            a <- freshVar
            forM_ fields (\field -> do
                fieldType <- inferL left field right
                firstPart <- sequence [freshVar | _ <- takeWhile (/= field) fields]
                secondPart <- sequence [freshVar | _ <- [length firstPart + 1 .. length fields]]
                constrain a (DataType name (firstPart ++ fieldType : secondPart)))
            return a
        infer2 = do
            a <- freshVar
            forM_ fields (\field -> do
                fieldType <- inferL left field right
                constrain Ok fieldType)
            return a
        infer3 = do
            fun <- freshVar
            arg <- freshVar
            res <- freshVar
            constrain fun (SufArrow arg res)
            return fun
        infer4 = do
            fun <- freshVar
            arg <- freshVar
            res <- freshVar
            constrain fun (NecArrow arg res)
            return fun
        infer5 = do
            a <- freshVar
            constrain a (DataType ("DATA\\" ++ name) [])
            return a
    Match m matches -> do
        res <- freshVar
        forM_ matches (\((name, vars), body) -> do
            mTypeVar    <- freshVar
            bodyTypeVar <- freshVar
            bs <- sequence [freshVar | _ <- vars]
            let subs = zip vars bs
                patternType = apply subs (promoteCons name vars)
            DataType "" [mType, bodyType] <- inferL left (Data "" [m, body]) right
            constrain res bodyType
            constrain bodyTypeVar bodyType
            constrain mTypeVar mType
            constrain patternType mTypeVar
            forM_ subs (\(x,b) -> do
                bodyType <- inferL left body [(Var x, Mono b)]
                constrain res bodyType))
        return res

promoteCons :: Constructor -> [TypeVar] -> Type
promoteCons name vars = DataType name (map TypeVar vars)

constrain :: Type -> Type -> Infer ()
constrain a b = modify (\s -> s{constraints = (a, b) : constraints s})

freshVar :: Infer Type
freshVar = do
    s <- get
    let uid = count s
    put s{count = uid + 1}
    return $ TypeVar $ show uid

nat = DataType "Nat" []
succ = Var "succ"
succT = Mono (SufArrow nat nat)
zero = Var "zero"
zeroT = Mono nat

infer :: Env -> Term -> Env -> IO ()
infer left term right = do
    inferRight left term
    inferLeft left term right

inferRight :: Env -> Term -> IO ()
inferRight left term = do
    let j = runStateT (inferR left term) initInferState
    mapM_ (\(a, b) -> print Judgement{left, right=[(term, Mono a)]} >> print b) j

inferLeft :: Env -> Term -> Env -> IO ()
inferLeft left term right = do
    let j = runStateT (inferL left term right) initInferState
    mapM_ (\(a, b) -> print Judgement{left=left ++ [(term, Mono a)], right} >> print b) j

testVar :: IO ()

testVar = infer [] (Var "x") []

testVarRight :: IO ()
testVarRight = infer [(Var "x", Mono nat)] (Var "x") []

testVarLeft :: IO ()
testVarLeft = infer [] (Var "x") [(Var "x", Mono nat)]

testApp0 :: IO ()
testApp0 = infer [] (App (Var "x") (Var "y")) []

testApp1 :: IO ()
testApp1 = infer [(succ, succT), (zero, zeroT)] (App succ zero) []

testAbs :: IO ()
testAbs = infer [] (Abs "id" "x" (Var "x")) []

example :: IO ()
example = inferRight [(Var "f", Poly [] [] $ NecArrow (DataType "[]" []) Ok)] (Abs "" "x" (App (Var "f") (Var "x")))

testK1 :: IO ()
testK1 = inferRight [] (Abs "" "x" (Abs "" "y" (Var "x")))

testK2 :: IO ()
testK2 = inferRight [] (Abs "" "x" (Abs "" "y" (Var "y")))

instance Show InferState where
    show :: InferState -> String
    show InferState{constraints} = "  where " ++ show constraints