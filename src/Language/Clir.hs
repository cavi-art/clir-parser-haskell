{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE OverloadedStrings #-}
module Language.Clir where

import Prelude hiding ((.), id)
import Control.Category
import Data.Scientific as Scientific
import Data.Text (Text)
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

data ConstValue = ConstString Text
                | ConstInt Int
                | ConstNumber Scientific
                | ConstBool Bool
                deriving (Show, Eq, Ord, Generic)

type FunName = Text

data FunctionDefinition = FunDef FunName [TypedVar] [TypedVar] [Contract] GeneralExpression
                        deriving (Show, Eq, Ord, Generic)


data CaseAltPattern = CConstant ConstValue ClirType
                    | CConstructor DataConstructor [AtomicExpression]
                    | CDefault
                 deriving (Show, Eq, Ord, Generic)

data CaseAltExpr = CaseAlt CaseAltPattern GeneralExpression
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


typeSig :: Grammar g (Sexp :- t) (ClirType :- t)
typeSig = iso fromSexp toSexp
  where fromSexp (Atom _ (AtomSymbol a)) = SimpleType a
        fromSexp (Atom _ _) = error "Unexpected atom type different from symbol"
        fromSexp (List _ []) = UnitType
        -- fromSexp (List _ [Quoted _ (Atom _ (AtomSymbol a))]) = TypeVar a
        fromSexp (List _ l) = CompoundType (map fromSexp l)
        fromSexp (Vector _ _) = error "Unexpected vector in type"
        fromSexp (Quoted _ (Atom _ (AtomSymbol a))) = TypeVar a
        fromSexp (Quoted _ a) = error $ "Unexpected quoted value" ++ show a
        toSexp (SimpleType a) = (Atom Sexp.dummyPos (AtomSymbol a))
        toSexp (UnitType) = (List Sexp.dummyPos [])
        -- toSexp (TypeVar a) = (List Sexp.dummyPos [(Quoted Sexp.dummyPos (Atom Sexp.dummyPos (AtomSymbol a)))])
        toSexp (TypeVar a) = Quoted Sexp.dummyPos (Atom Sexp.dummyPos (AtomSymbol a))
        toSexp (CompoundType l) = (List Sexp.dummyPos (map toSexp l))

instance SexpIso ClirType where
  sexpIso = typeSig


clirbool :: Grammar SexpGrammar (Sexp :- b) (Bool :- b)
clirbool = coproduct [ bool, sym "true" >>> push True, sym "false" >>> push False ]


-- | Constant nodes are used in different nodes of the grammar (case
-- alternatives and constants).
constantNode :: Grammar SexpGrammar (Sexp :- t) (ConstValue :- t)
constantNode = match
               $ With (\str -> str . string)
               $ With (\int_ -> int_ . int)
               $ With (\real_ -> real_ . real)
               $ With (\bool_ -> bool_ . clirbool)
               $ End


clir_constant :: Grammar SexpGrammar (Sexp :- t) (ClirType :- (ConstValue :- t))
clir_constant = (list (
                   el (sym "the")  >>>
                   el sexpIso      >>>
                   el constantNode >>> swap))


-- | Constructor applications are used in the grammar both for
-- destructuring in case alternatives and literal constructor
-- applications
clir_constructorApp :: Grammar SexpGrammar (Sexp :- b) ([AtomicExpression] :- (Text :- b))
clir_constructorApp = (list (el (sym "@@") >>>
                             el symbol >>>
                             rest sexpIso))


instance SexpIso AtomicExpression where
  sexpIso = match
    $ With (\var -> var . symbol)
    $ With (\const -> const . clir_constant)
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
    $ With (\constra -> constra . clir_constructorApp)
    $ With (\tuple -> tuple . (list (el (sym "tuple") >>>
                                     rest sexpIso)))
    $ End


typedVar :: Grammar SexpGrammar (Sexp :- t) (TypedVar :- t)
typedVar = match
  $ With (\typedvar -> typedvar . list (el symbol >>> el typeSig))
  $ End

instance SexpIso TypedVar where
  sexpIso = typedVar


typedVarList :: Grammar SexpGrammar (Sexp :- t) ([TypedVar] :- t)
typedVarList = sexpIso


-- |TODO: Handle pre/post conditions
--
-- Idea: map sexp to a haskell Map and then get each element out of
-- the contract, because they can be anywhere in any order; e.g.,
-- (declare (x) (y) (assertions (precd ...)) (z))
contracts :: Grammar SexpGrammar (Sexp :- t) ([Contract] :- t)
contracts = undefined


funDecl :: Grammar SexpGrammar (Sexp :- t) (FunctionDefinition :- t)
funDecl = match
  $ With (\fdef -> fdef . coproduct [ list (el symbol       >>>
                                            el typedVarList >>>
                                            el typedVarList >>>
                                            el contracts    >>>
                                            el sexpIso)
                                    , list (el symbol       >>>
                                            el typedVarList >>>
                                            el typedVarList >>>
                                            push []         >>>
                                            el sexpIso)
                                    ])
  $ End


instance SexpIso FunctionDefinition where
  sexpIso = funDecl


funDeclList :: Grammar SexpGrammar (Sexp :- t) ([FunctionDefinition] :- t)
funDeclList = sexpIso


caseAltPattern :: Grammar SexpGrammar (Sexp :- t) (CaseAltPattern :- t)
caseAltPattern = match
  $ With (\cconstant -> cconstant . clir_constant)
  $ With (\cconstructor -> cconstructor . clir_constructorApp)
  $ With (\cdefault -> cdefault . sym "default")
  $ End


caseAltExpr :: Grammar SexpGrammar (Sexp :- t) (CaseAltExpr :- t)
caseAltExpr = match
  $ With (\casealt -> casealt . list (el caseAltPattern >>> el sexpIso))
  $ End

instance SexpIso GeneralExpression where
  sexpIso = match
    $ With (\be -> be . sexpIso)
    $ With (\let_ -> let_ . (list (el (sym "let")
                                   >>>
                                   el typedVarList
                                   >>>
                                   el sexpIso -- BindingExpression
                                   >>>
                                   el sexpIso -- GeneralExpression
                                  )))
    $ With (\letfun -> letfun . (list (el (sym "letfun")
                                       >>>
                                       el funDeclList
                                       >>>
                                       el sexpIso
                                      )))
    $ With (\case_ -> case_ . (list (el (sym "case") >>> el sexpIso >>> rest caseAltExpr)))
    $ End


t = encode $ Const (ConstString "5") (SimpleType "int")

t2 :: Either String GeneralExpression
t2 = decode "(let ((x int)) (@ f (the bool false)) x)"

t3  :: Either String BindingExpression
t3 = decode "(the (array 'a) \"x\")"

r :: Either a b -> b
r (Right x) = x

t4 :: Either String GeneralExpression
t4 = decode "(case x ((the int 1) (the int 1)) (default x))"
