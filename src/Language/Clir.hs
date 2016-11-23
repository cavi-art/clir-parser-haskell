{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}
module Language.Clir where

import Prelude hiding ((.), id)
import Control.Arrow ((>>>))
import Control.Category
import Data.Data (Data)
import Data.Scientific as Scientific
import Data.Text (Text, pack, unpack)
import qualified Language.Sexp as Sexp
import Language.SexpGrammar
import Language.SexpGrammar.Generic

import GHC.Generics (Generic)

-- Types
data ClirType = UnitType
              | SimpleType Text
              | TypeVar Text
              | CompoundType [ClirType]
              deriving (Show, Eq, Ord, Generic)

type Formula = String

type DataConstructor = Text

-- Typed variable definitions
data TypedVar = TypedVar Text ClirType
              deriving (Show, Eq, Ord, Generic)

data Contract = PreCD Formula
              | PostCD Formula
              | Variant Formula
              deriving (Show, Eq, Ord, Generic)

type VarName = Text
type ConstValue = Text
type FunName = Text

data FunctionDefinition = FunDef FunName [TypedVar] [TypedVar] [Contract] GeneralExpression
                        deriving (Show, Eq, Ord, Generic)


data CaseAltExpr = CConstant String ClirType
                 | CConstructor DataConstructor [AtomicExpression]
                 | CDefault
                 deriving (Show, Eq, Ord, Generic)


-- Atomic Expressions
data AtomicExpression = Var VarName
                      | Const ConstValue ClirType
                      deriving (Show, Eq, Ord, Generic)

-- Binding Expressions
data BindingExpression = AtomE AtomicExpression
                       | FunA FunName [AtomicExpression]
                       | ConstrA DataConstructor [AtomicExpression]
                       | Tuple [AtomicExpression]
                       deriving (Show, Eq, Ord, Generic)

-- General Expressions
data GeneralExpression = Binding BindingExpression
                       | Let [TypedVar] BindingExpression GeneralExpression
                       | LetFun [FunctionDefinition] GeneralExpression
                       | Case AtomicExpression [CaseAltExpr]
                       deriving (Show, Eq, Ord, Generic)




varGrammar = symbol

constNumberGrammar = t
  where t = list (el (sym "the") >>>
                  el (sym "int") >>>
                  el real)

constStringGrammar = list (el (sym "the") >>>
                           el (sym "string") >>>
                           el string)

constTrueGrammar = list (el (sym "the") >>>
                         el (sym "bool") >>>
                         el (sym "true"))

constFalseGrammar = list (el (sym "the") >>>
                          el (sym "bool") >>>
                          el (sym "false"))

t1 = decodeWith constStringGrammar "(the string \"hello, world\")" :: Either String Text


showToSymbol :: (Read a, Show a) => Grammar SexpGrammar (a :- t) (Text :- t)
showToSymbol = iso fromSci toSci
  where fromSci s = pack $ show s
        toSci t = read $ unpack t

anyatom :: Grammar SexpGrammar (Sexp :- t) (Text :- t)
anyatom = coproduct
  [
    string -- TODO: Distinguish string and symbol
  , symbol
  , showToSymbol . real
  , showToSymbol . int
  ]


instance SexpIso ClirType where
  sexpIso = iso fromSexp toSexp
    where fromSexp (Atom _ (AtomSymbol a)) = SimpleType a
          fromSexp (List _ []) = UnitType
          fromSexp (List _ [Quoted _ (Atom _ (AtomSymbol a))]) = TypeVar a
          fromSexp (List _ l) = CompoundType (map fromSexp l)
          toSexp (SimpleType a) = (Atom Sexp.dummyPos (AtomSymbol a))
          toSexp (UnitType) = (List Sexp.dummyPos [])
          toSexp (TypeVar a) = (List Sexp.dummyPos [(Quoted Sexp.dummyPos (Atom Sexp.dummyPos (AtomSymbol a)))])
          toSexp (CompoundType l) = (List Sexp.dummyPos (map toSexp l))



instance SexpIso AtomicExpression where
  sexpIso = match
    $ With (\var -> var . symbol)
    $ With (\const -> const . (list (
                                  el (sym "the") >>>
                                  el sexpIso >>>
                                  el anyatom >>>
                                  swap)))
    $ End


-- -- Binding Expressions
-- data BindingExpression = AtomE AtomicExpression
--                        | FunA FunName [AtomicExpression]
--                        | ConstrA DataConstructor [AtomicExpression]
--                        | Tuple [AtomicExpression]
--                        deriving (Show, Eq, Ord, Generic)

instance SexpIso BindingExpression where
  sexpIso = match
    $ With (\atome -> atome . sexpIso)
    $ With (\funa -> funa . (list (el (sym "@") >>>
                                   el symbol >>>
                                   rest sexpIso)))
    $ With (\constra -> constra . (list (el (sym "@@") >>>
                                         el symbol >>>
                                         rest sexpIso)))
    $ With (\tuple -> tuple . (list (el (sym "tuple") >>>
                                     rest sexpIso)))
    $ End


t = encode $ Const "5" (SimpleType "int")

t2 = decode "(@ f (the int false))" :: Either String AtomicExpression
