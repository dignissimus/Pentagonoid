{-# LANGUAGE GADTs #-}

module Data where

data Symbol = Symbol String | Identifier Integer | Unknown deriving (Show, Eq)

type ExpressionType = Symbol

data Expression
  = Composition Expression Expression
  | Ap Expression Expression
  | FunctionApplication Expression [Expression]
  | IdentityPath
  | Literal Symbol
  | Nil
  | Cons Expression Expression
  | IdentityFunction ExpressionType
  | Lambda Symbol Expression
  deriving (Show)

joinPaths :: [Expression] -> Expression
joinPaths = foldr1 Composition
