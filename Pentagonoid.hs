{-# LANGUAGE OverloadedRecordDot #-}

module Pentagonoid where

import Data (Expression (Ap, Composition, FunctionApplication, Lambda, Literal, Nil), Symbol (Identifier, Symbol), joinPaths)
import Rewrite

proveEquality :: Expression -> Expression -> Proof
proveEquality leftExpression rightExpression = undefined

listConcat = Literal (Symbol "++")

xs :: Expression
xs = Literal (Symbol "xs")

ys :: Expression
ys = Literal (Symbol "ys")

zs :: Expression
zs = Literal (Symbol "zs")

x :: Symbol
x = Identifier 0

concatAssoc = Literal (Symbol "++-assoc")

-- ++-assoc ([] ++ xs) ys zs ∙ ++-assoc [] xs (ys ++ zs)
leftExpression :: Expression
leftExpression =
  joinPaths
    [ FunctionApplication
        concatAssoc
        [ FunctionApplication listConcat [Nil, xs],
          ys,
          zs
        ],
      FunctionApplication
        concatAssoc
        [ Nil,
          xs,
          FunctionApplication listConcat [ys, zs]
        ]
    ]

-- ap (_++ zs) (++-assoc [] xs ys) ∙ ++-assoc [] (xs ++ ys) zs ∙ ap (_++_ []) (++-assoc xs ys zs)
rightExpression :: Expression
rightExpression =
  joinPaths
    [ Ap
        (Lambda x (FunctionApplication listConcat [Literal x, zs]))
        (FunctionApplication concatAssoc [Nil, xs, ys]),
      FunctionApplication
        concatAssoc
        [ Nil,
          FunctionApplication listConcat [xs, ys],
          zs
        ],
      Ap
        (Lambda x (FunctionApplication listConcat [Nil, Literal x]))
        (FunctionApplication concatAssoc [xs, ys, zs])
    ]

leftReduction :: [ProofStep]
leftReduction = simplify leftExpression

rightReduction :: [ProofStep]
rightReduction = simplify rightExpression

main = do
  print leftReduction
  print rightReduction
