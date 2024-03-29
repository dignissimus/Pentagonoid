{-# LANGUAGE GADTs #-}

module Data where

data Symbol = Symbol String | Identifier Integer | Unknown deriving (Eq)

instance Show Symbol where
  show :: Symbol -> String
  show (Symbol s) = s
  show (Identifier n) = "a" ++ show n
  show Unknown = "_"

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
  deriving (Eq)

quote :: Expression -> String
quote = ("(" ++) . (++ ")") . show

show' :: Expression -> [String]
show' (Composition left right) = [quote left, "∙", quote right]
show' (Ap f p) = ["ap", quote f, quote p]
show' (FunctionApplication f xs) = quote f : map quote xs
show' IdentityPath = ["idp _"]
show' (Literal sym) = [show sym]
show' Nil = ["[]"]
show' (Cons x xs) = [quote x, "∷", quote xs]
show' (IdentityFunction _) = ["idfun _"]
show' (Lambda sym e) = ["λ", show sym, "→", quote e]

instance Show Expression where
  show :: Expression -> String
  show = unwords . show'

joinPaths :: [Expression] -> Expression
joinPaths = foldr1 Composition
