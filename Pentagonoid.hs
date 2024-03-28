module Pentagonoid where

import Data (Expression (Ap, Composition, Cons, FunctionApplication, Lambda, Literal, Nil), Symbol (Identifier, Symbol), joinPaths)
import Rewrite (Proof, ProofStep (..), reduceExpression)

proveEquality :: Expression -> Expression -> Proof
proveEquality leftExpression rightExpression = undefined

listConcat :: Expression
listConcat = Literal (Symbol "++")

xs :: Expression
xs = Literal (Symbol "xs")

ys :: Expression
ys = Literal (Symbol "ys")

zs :: Expression
zs = Literal (Symbol "zs")

ws :: Expression
ws = Literal (Symbol "ws")

p :: Symbol
p = Symbol "p"

x :: Expression
x = Literal $ Symbol "x"

y :: Expression
y = Literal $ Symbol "y"

z :: Expression
z = Literal $ Symbol "z"

w :: Expression
w = Literal $ Symbol "w"

concatAssoc = Literal (Symbol "++-assoc")

lhs :: Expression -> Expression -> Expression -> Expression -> Expression
lhs xs ys zs ws =
  joinPaths
    [ FunctionApplication
        concatAssoc
        [ FunctionApplication listConcat [ws, xs],
          ys,
          zs
        ],
      FunctionApplication
        concatAssoc
        [ ws,
          xs,
          FunctionApplication listConcat [ys, zs]
        ]
    ]

rhs :: Expression -> Expression -> Expression -> Expression -> Expression
rhs xs ys zs ws =
  joinPaths
    [ Ap
        (Lambda p (FunctionApplication listConcat [Literal p, zs]))
        (FunctionApplication concatAssoc [ws, xs, ys]),
      FunctionApplication
        concatAssoc
        [ ws,
          FunctionApplication listConcat [xs, ys],
          zs
        ],
      Ap
        (Lambda p (FunctionApplication listConcat [ws, Literal p]))
        (FunctionApplication concatAssoc [xs, ys, zs])
    ]

-- ++-assoc ([] ++ xs) ys zs ∙ ++-assoc [] xs (ys ++ zs)
leftExpression :: Expression
leftExpression = lhs xs ys zs Nil

-- ap (_++ zs) (++-assoc [] xs ys) ∙ ++-assoc [] (xs ++ ys) zs ∙ ap (_++_ []) (++-assoc xs ys zs)
rightExpression :: Expression
rightExpression = rhs xs ys zs Nil

simplify :: Expression -> Expression
simplify expression =
  case reduceExpression expression of
    [] -> expression
    ls -> expression where ProofStep _ expression = last ls

leftReduction :: [ProofStep]
leftReduction = reduceExpression leftExpression

rightReduction :: [ProofStep]
rightReduction = reduceExpression rightExpression

main :: IO ()
main = do
  print leftReduction
  print rightReduction
