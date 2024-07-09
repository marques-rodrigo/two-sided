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

verbose :: Bool
verbose = False

debug :: Applicative f => String -> f ()
debug = when verbose . traceM

type Infer a = StateT InferState [] a
data InferState = InferState {count :: Int, constraints :: ConstraintSet}
    deriving (Eq)

initInferState :: InferState
initInferState = InferState {count = 0, constraints = []}

inferR :: Env -> Term -> Infer Judgement
inferR left term = do
    debug $ "Inferring on the right with " ++ show left ++ " for " ++ show term
    case term of
        Var x -> do
            b <- freshVar
            case lookup term left of
                Nothing -> do
                    debug "Closed by VarK on the right"
                    constrain Ok b
                    return Judgement{left = left, right = [(term, Mono b)]}
                Just (Mono t) -> do
                    debug "Closed by Var  on the right"
                    constrain t b
                    return Judgement{left = left, right = [(term, Mono b)]}
                Just (Poly vars rels ty) -> do
                    debug "Closed by GVar  on the right"
                    bs <- sequence [freshVar | _ <- vars]
                    let subs = mkSubsts vars bs
                        instType = applyMany subs ty
                        instRels = applyMany subs rels
                    constrain instType b
                    modify (\s -> s{constraints = instRels ++ constraints s}) -- fixme
                    return Judgement{left = left, right = [(term, Mono b)]}
        App m n -> do
            debug "Proceeding by AppR"
            a <- freshVar
            Judgement{right = [(_, Mono b)]} <- inferR left m
            Judgement{right = [(_, Mono c)]} <- inferR left n
            constrain b (SufArrow c a)
            return $ Judgement{left = left, right = [(term, Mono a)]}
        Abs f x body -> inferNecessity <|> inferSufficiency
          where
            inferSufficiency = do
                debug $ "Proceeding by AbsR"
                a <- freshVar
                t <- freshVar
                let left' =
                        (Var "x", Mono t) : case f of
                            "" -> left
                            _ -> (Var f, Mono a) : left
                Judgement{right = right'} <- inferR left' body
                let Mono b = fromJust $ lookup body right'
                constrain (SufArrow t b) a
                return Judgement{left = left, right = [(term, Mono a)]}
            inferNecessity = do
                debug $ "Proceeding by AbnR"
                a <- freshVar
                t <- freshVar
                let left' = case f of
                        "" -> left
                        _ -> (Var f, Mono a) : left
                Judgement{left = left'} <- inferL left' body [(Var "x", Mono t)]
                let Mono b = fromJust $ lookup body left'
                constrain (NecArrow t b) a
                return Judgement{left = left, right = [(term, Mono a)]}
        Data name fields -> do
            debug $ "Proceeding by CnsR"
            a <- freshVar
            fieldJudgements <- mapM (inferR left) fields
            let fieldTypes = map (toType . snd . head . right) fieldJudgements
            constrain (DataType name fieldTypes) a
            return Judgement{left = left, right = [(term, Mono a)]}
        Match m matches -> do
            debug $ "Proceeding by MchR"
            a <- freshVar
            Judgement{right = [(_, Mono b)]} <- inferR left m
            mapM_ (inferRMatching left a b) matches
            return Judgement{left = left, right = [(term, Mono a)]}
          where
            inferRMatching left resType mType ((name, vars), term) = do
                bs <- sequence [freshVar | _ <- vars]
                let left' = zipWith (\x v -> (Var x, Mono v)) vars bs ++ left
                Judgement{right = [(_, Mono t)]} <- inferR left' term
                let patternType = DataType name (map TypeVar vars)
                    subs = mkSubsts vars bs
                    patternType' = applyMany subs patternType
                constrain t resType
                constrain mType patternType'

inferL :: Env -> Term -> Env -> Infer Judgement
inferL left term right = do
    debug $ "Inferring on the left with " ++ show left ++ " for " ++ show term ++ " with " ++ show right
    case right of
        [(Var x, b)] -> do
            debug $ "Closed by VarK on the left"
            a <- freshVar
            constrain Ok (toType b)
            return Judgement{left = (term, Mono a) : left, right = right}
        _ -> fail ""
    <|> inferL' left term right

inferL' :: Env -> Term -> Env -> Infer Judgement
inferL' left term right = case term of
    Var x -> do
        case lookup term right of
            Nothing -> fail "Lookup fail on the right"
            Just b -> do
                debug $ "Closed by Var2 on the left"
                a <- freshVar
                constrain a (toType b)
                return Judgement{left = (term, Mono a) : left, right = right}
    App m n -> infer1 <|> infer2
      where
        infer1 = do
            debug $ "Proceeding by AppL"
            a <- freshVar
            Judgement{right = right'} <- inferR left m
            let (Mono b) = fromJust $ lookup m right'
            Judgement{left = left'} <- inferL left n right
            let (Mono c) = fromJust $ lookup n left'
            constrain b (NecArrow c a)
            return Judgement{left = (term, Mono a) : left, right = right}
        infer2 = do
            debug $ "Proceeding by FunK on the left"
            a <- freshVar
            Judgement{left = left'} <- inferL left m right
            let Mono b = fromJust $ lookup m left'
            constrain Ok (NecArrow a b)
            return Judgement{left = (term, Mono a) : left, right = right}
    Abs _ x m -> do
        debug $ "Closed by AbsDL on the left"
        a <- freshVar
        constrain a (DataType "DATA" []) -- express every data type in the language with this simple trick
        return Judgement{left = (term, Mono a) : left, right = right}
    Data name fields -> infer1 <|> infer2 <|> infer3 <|> infer4 <|> infer5
      where
        infer1 = do
            debug $ "Proceeding by CnsL"
            a <- freshVar
            constrain a (DataType ("DATA\\" ++ name) [])
            field <- lift fields
            -- fieldJudgements <- mapM (\field -> inferL left field right) fields
            Judgement{left = (field, fieldType) : _} <- inferL left field right
            firstPart <- sequence [freshVar | _ <- takeWhile (/= field) fields]
            secondPart <- sequence [freshVar | _ <- [length firstPart + 1 .. length fields]]
            constrain a (DataType name (firstPart ++ toType fieldType : secondPart))
            return Judgement{left = (term, Mono a) : left, right = right}
        infer2 = do
            debug $ "Proceeding by CnsK on the left"
            a <- freshVar
            field <- lift fields
            Judgement{left = (field, fieldType) : _} <- inferL left field right
            constrain Ok (toType fieldType)
            return Judgement{left = (term, Mono a) : left, right = right}
        infer3 = do
            debug $ "Closed by CnsDL1 on the left"
            a <- freshVar
            b <- freshVar
            c <- freshVar
            constrain a (SufArrow b c)
            return Judgement{left = (term, Mono a) : left, right = right}
        infer4 = do
            debug $ "Closed by CnsDL2 on the left"
            a <- freshVar
            b <- freshVar
            c <- freshVar
            constrain a (NecArrow b c)
            return Judgement{left = (term, Mono a) : left, right = right}
        infer5 = do
            debug $ "Closed by CnsDL3 on the left"
            a <- freshVar
            constrain a (DataType ("DATA\\" ++ name) [])
            return Judgement{left = (term, Mono a) : left, right = right}
    Match m matches -> do
        debug "Proceeding by MchL"
        a <- freshVar
        forM_ matches (\(pi@(name, vars), body) -> do
            (ai, bi) <- liftM2 (,) freshVar freshVar
            bs <- sequence [freshVar | _ <- vars]
            let bMap = zip vars bs
                pair = Data "(,)" [m, body]
            Judgement{left = left'} <- inferL left pair right
            let (Mono ai') = fromJust $ lookup pair left'
            constrain a ai
            constrain (DataType "(,)" [ai, bi]) ai'
            let subs = mkSubsts vars bs
                inst = applyMany subs (DataType name (map TypeVar vars))
            constrain inst bi
            forM_ vars (\x -> do
                bix <- freshVar
                Judgement{left = left'} <- inferL left body [(Var x, Mono (fromJust $ lookup x bMap))]
                let (Mono aix) = fromJust $ lookup body left'
                constrain a aix))
        return Judgement{left = (term, Mono a) : left, right = right}

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
    mapM_ (\(a, b) -> print a >> print b) j

inferLeft :: Env -> Term -> Env -> IO ()
inferLeft left term right = do
    let j = runStateT (inferL left term right) initInferState
    mapM_ (\(a, b) -> print a >> print b) j

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

instance Show InferState where
    show :: InferState -> String
    show InferState{constraints} = "  where " ++ show constraints