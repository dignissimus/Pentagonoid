module Rewrite where

import Control.Monad
import Data
import Data.List
import Data.Maybe

data RewriteRule
  = AbsurdRule
  | LeftIdentity
  | RightIdentity
  | ApplyIdentityFunction
  | EtaReduction
  | ApId
  | NilConcatOne
  | NilConcatTwo
  | ConstantFunction
  | ConcatAssocNil
  | ConcatAssocCons
  | ConsConcat
  deriving (Show)

data Justification = Justification RewriteRule | Evident deriving (Show)

data ProofStep = ProofStep Justification Expression deriving (Show)

type RewriteRuleDefinition = Expression -> Maybe ProofStep

type FunctionRewrite = Expression -> Maybe (Expression, Justification)

data Proof = Proof
  { start :: Expression,
    steps :: [ProofStep],
    -- Redundant
    end :: Expression
  }

-- TODO: Ensure expressions are associated in the nice way
reductionStep :: Expression -> Maybe (ProofStep, Expression)
reductionStep expression = foldr (mplus . flip applyRewrite expression) Nothing rewriteRules

reductionStepRecursive :: Expression -> Maybe (ProofStep, Expression)
reductionStepRecursive expression@(Composition left right) =
  foldr
    mplus
    Nothing
    [ reductionStep expression,
      do
        (ProofStep justification left', _) <- reductionStepRecursive left
        let expression' = Composition left' right
        let proofStep = ProofStep justification expression'
        return (proofStep, expression'),
      do
        (ProofStep justification right', _) <- reductionStepRecursive right
        let expression' = Composition left right'
        let proofStep = ProofStep justification expression'
        return (proofStep, expression')
    ]
reductionStepRecursive expression@(Ap f path) =
  foldr
    mplus
    Nothing
    [ reductionStep expression,
      do
        (ProofStep justification f', _) <- reductionStepRecursive f
        let expression' = Ap f' path
        let proofStep = ProofStep justification expression'
        return (proofStep, expression'),
      do
        (ProofStep justification path', _) <- reductionStepRecursive path
        let expression' = Ap f path'
        let proofStep = ProofStep justification expression'
        return (proofStep, expression')
    ]
reductionStepRecursive expression@(Lambda parameter body) =
  foldr
    mplus
    Nothing
    [ reductionStep expression,
      do
        (ProofStep justification body', _) <- reductionStepRecursive body
        let expression' = Lambda parameter body'
        let proofStep = ProofStep justification expression'
        return (proofStep, expression')
    ]
reductionStepRecursive expression@(FunctionApplication f xs) =
  foldr
    mplus
    Nothing
    [ reductionStep expression,
      do
        (ProofStep justification f', _) <- reductionStepRecursive f
        let expression' = FunctionApplication f' xs
        let proofStep = ProofStep justification expression'
        return (proofStep, expression'),
      do
        let (left, right) = span (isNothing . reductionStepRecursive) xs
        (r, rs) <- uncons right
        (ProofStep justification r', _) <- reductionStepRecursive r
        let expression' = FunctionApplication f (left ++ (r' : rs))
        let proofStep' = ProofStep justification expression'
        return (proofStep', expression')
    ]
reductionStepRecursive expression@(Cons left right) =
  foldr
    mplus
    Nothing
    [ reductionStep expression,
      do
        (ProofStep justification left', _) <- reductionStepRecursive left
        let expression' = Cons left' right
        let proofStep = ProofStep justification expression'
        return (proofStep, expression'),
      do
        (ProofStep justification right', _) <- reductionStepRecursive right
        let expression' = Cons left right'
        let proofStep = ProofStep justification expression'
        return (proofStep, expression')
    ]
reductionStepRecursive expression = reductionStep expression

reduceExpression :: Expression -> [ProofStep]
reduceExpression = unfoldr reductionStepRecursive

-- TODO: NilConcatTwo,
rewriteRules :: [RewriteRule]
rewriteRules =
  [ -- Rule used for testing
    AbsurdRule,
    -- Eliminate the identity path on the left, re-associating as required
    LeftIdentity,
    -- Eliminate the identity path on the right, re-associating as required
    RightIdentity,
    -- Eliminate applications of the identity function
    ApplyIdentityFunction,
    -- Apply eta reduction
    EtaReduction,
    -- Use the functoriality of Ap to rewrite Ap id as id
    ApId,
    -- Use the definition of list concatenation to reduce (Nil ++) to the identity
    NilConcatOne,
    -- Use the definition of list concatenation to reduce (Nil ++ xs) to txs
    NilConcatTwo,
    -- Reduce constant functions to the identity function
    ConstantFunction,
    --
    ConcatAssocNil,
    ConcatAssocCons,
    ConsConcat
  ]

applyRewrite :: RewriteRule -> Expression -> Maybe (ProofStep, Expression)
applyRewrite = ((transform <$>) .) . applyRewrite'
  where
    transform ps@(ProofStep justification expression) = (ps, expression)

applyRewrite' :: RewriteRule -> Expression -> Maybe ProofStep
applyRewrite' AbsurdRule = applyAbsurdRule
applyRewrite' LeftIdentity = applyLeftIdentity
applyRewrite' RightIdentity = applyRightIdentity
applyRewrite' ApplyIdentityFunction = applyApplyIdentityFunction
applyRewrite' EtaReduction = applyEtaReduction
applyRewrite' ApId = applyApId
applyRewrite' NilConcatOne = applyNilConcatOne
applyRewrite' NilConcatTwo = applyNilConcatTwo
applyRewrite' ConstantFunction = applyConstantFunction
applyRewrite' ConcatAssocNil = applyConcatAssocNil
applyRewrite' ConcatAssocCons = applyConcatAssocCons
applyRewrite' ConsConcat = applyConsConcat

applyAbsurdRule :: RewriteRuleDefinition
applyAbsurdRule (Literal (Symbol "absurd-x")) = do
  return $ ProofStep Evident (Literal (Symbol "absurd-y"))
applyAbsurdRule _ = Nothing

reduceLeftIdentity :: Expression -> Maybe Expression
reduceLeftIdentity (Composition IdentityPath expression) = Just expression
reduceLeftIdentity (Composition composition@(Composition _ right) expression) = reduceLeftIdentity $ Composition right expression
reduceLeftIdentity _ = Nothing

reduceRightIdentity :: Expression -> Maybe Expression
reduceRightIdentity (Composition expression IdentityPath) = Just expression
reduceRightIdentity (Composition expression composition@(Composition left _)) = reduceRightIdentity $ Composition expression left
reduceRightIdentity _ = Nothing

applyLeftIdentity :: RewriteRuleDefinition
applyLeftIdentity expression = do
  right <- reduceLeftIdentity expression
  return $ ProofStep (Justification LeftIdentity) right

applyRightIdentity :: RewriteRuleDefinition
applyRightIdentity expression = do
  left <- reduceRightIdentity expression
  return $ ProofStep (Justification RightIdentity) left

applyApplyIdentityFunction :: RewriteRuleDefinition
applyApplyIdentityFunction (FunctionApplication (IdentityFunction _) [expression]) = do
  return $ ProofStep Evident expression
applyApplyIdentityFunction _ = Nothing

etaReduce :: FunctionRewrite
etaReduce (Lambda x (FunctionApplication f@(Literal (Symbol f')) [Literal x'])) =
  if x == x'
    then Just (f, Evident)
    else Nothing
etaReduce _ = Nothing

constantFunctionReduce :: FunctionRewrite
constantFunctionReduce (Lambda x (Literal x')) =
  if x == x'
    then Just (IdentityFunction Unknown, Evident)
    else Nothing
constantFunctionReduce _ = Nothing

rewriteFunction :: FunctionRewrite -> RewriteRuleDefinition
rewriteFunction rewrite (Ap f p) = do
  (f', justification) <- rewrite f
  return $ ProofStep justification (Ap f' p)
rewriteFunction rewrite (FunctionApplication f xs) = do
  (f', justification) <- rewrite f
  return $ ProofStep justification (FunctionApplication f' xs)
rewriteFunction _ _ = Nothing

applyEtaReduction :: RewriteRuleDefinition
applyEtaReduction = rewriteFunction etaReduce

applyConstantFunction :: RewriteRuleDefinition
applyConstantFunction = rewriteFunction constantFunctionReduce

applyApId :: RewriteRuleDefinition
applyApId (Ap f IdentityPath) = Just $ ProofStep (Justification ApId) IdentityPath
applyApId (Ap (IdentityFunction _) p) = Just $ ProofStep (Justification ApId) p
applyApId _ = Nothing

nilConcatOne :: FunctionRewrite
nilConcatOne ((FunctionApplication (Literal (Symbol "++")) [Nil])) = Just (IdentityFunction Unknown, Evident)
nilConcatOne _ = Nothing

applyNilConcatOne :: RewriteRuleDefinition
applyNilConcatOne = rewriteFunction nilConcatOne

concat' xs ys = FunctionApplication (Literal (Symbol "++")) [xs, ys]

-- TODO: Perhaps generalise these
applyNilConcatTwo :: Expression -> Maybe ProofStep
applyNilConcatTwo (FunctionApplication (Literal (Symbol "++")) [Nil, xs]) = Just $ ProofStep (Justification NilConcatTwo) xs
applyNilConcatTwo _ = Nothing

applyConsConcat :: Expression -> Maybe ProofStep
applyConsConcat (FunctionApplication (Literal (Symbol "++")) [Cons x xs, ys]) = Just $ ProofStep (Justification NilConcatTwo) (Cons x (concat' xs ys))
applyConsConcat _ = Nothing

applyConcatAssocNil :: Expression -> Maybe ProofStep
applyConcatAssocNil (FunctionApplication (Literal (Symbol "++-assoc")) [Nil, ys, zs]) = Just $ ProofStep (Justification NilConcatTwo) IdentityPath
applyConcatAssocNil _ = Nothing

x_ = Identifier 0

x_' = Literal x_

concatAssoc' xs ys zs = FunctionApplication (Literal (Symbol "++")) [xs, ys, zs]

consOne' x = FunctionApplication (Literal (Symbol "_∷_")) [x]

applyConcatAssocCons :: Expression -> Maybe ProofStep
applyConcatAssocCons (FunctionApplication (Literal (Symbol "++-assoc")) [Cons x xs, ys, zs]) = Just $ ProofStep (Justification NilConcatTwo) $ Ap (Lambda x_ (consOne' x_')) (concatAssoc' xs ys zs)
applyConcatAssocCons _ = Nothing
