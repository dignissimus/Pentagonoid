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
  | ApFusion
  | CustomRewrite CustomRewriteRule
  deriving (Show)

data RewriteRuleJustification
  = LeftIdentityRule
  | RightIdentityRule
  | ApFusionRule Expression Expression Expression
  | NilConcatTwoRule

data CustomRewriteRule deriving (Show)

data Justification
  = Justification RewriteRuleJustification
  | Evident
  | Symm RewriteRuleJustification
  | Hole

justify :: RewriteRuleJustification -> String
justify LeftIdentityRule = "sym (lUnit _)"
justify RightIdentityRule = "sym (rUnit _)"
justify (ApFusionRule f p q) = "sym (ap-compPath " ++ quote f ++ " " ++ quote p ++ " " ++ quote q ++ ")"
justify _ = ""

instance Show Justification where
  show :: Justification -> String
  show Evident = ""
  show (Symm r) =
    if justify r == ""
      then ""
      else " sym (" ++ justify r ++ ") "
  show (Justification r) =
    if justify r == ""
      then ""
      else " " ++ justify r ++ " "
  show Hole = " ? "

data ProofStep = ProofStep Justification Expression deriving (Show)

type RewriteRuleDefinition = Expression -> Maybe ProofStep

type FunctionRewrite = Expression -> Maybe (Expression, Justification)

data Proof = Proof
  { start :: Expression,
    steps :: [ProofStep],
    -- Redundant
    end :: Expression
  }

joinProofs :: Proof -> Proof -> Proof
joinProofs Proof {start, steps, end} Proof {start = start', steps = steps', end = end'} =
  if end == start'
    then
      Proof
        { start,
          steps = steps ++ steps',
          end = end'
        }
    else
      Proof
        { start,
          steps = steps ++ ProofStep Hole start' : steps',
          end = end'
        }

instance Show Proof where
  show :: Proof -> String
  show Proof {start, steps, end} =
    "    "
      ++ show start
      ++ go steps
    where
      go [] = ""
      go (s : ss) =
        "\n  ≡⟨"
          ++ show justificatoin
          ++ "⟩"
          ++ "\n    "
          ++ show expression
          ++ go ss
        where
          ProofStep justificatoin expression = s

mkProof :: Expression -> [ProofStep] -> Proof
mkProof start steps =
  Proof
    { start,
      steps = steps,
      end = expression
    }
  where
    ProofStep _ expression = last steps

symm :: Justification -> Justification
symm Evident = Evident
symm Hole = Hole
symm (Justification rewrite) = Symm rewrite

flipStep :: ProofStep -> ProofStep
flipStep (ProofStep justification expression) = ProofStep (symm justification) expression

reverseProof :: Proof -> Proof
reverseProof Proof {start, steps, end} =
  Proof
    { start = end,
      end = start,
      steps = steps'
    }
  where
    steps' = fmap (uncurry ProofStep) (zip justifications' expressions')
    justifications' = reverse justifications
    expressions' = drop 1 $ reverse (start : expressions)
    (justifications, expressions) = unzip . fmap (unwrap . flipStep) $ steps
    unwrap (ProofStep j e) = (j, e)

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
    ConsConcat,
    ApFusion
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
applyRewrite' ApFusion = applyApFusion

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
  return $ ProofStep (Justification LeftIdentityRule) right

applyRightIdentity :: RewriteRuleDefinition
applyRightIdentity expression = do
  left <- reduceRightIdentity expression
  return $ ProofStep (Justification RightIdentityRule) left

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
applyApId (Ap f IdentityPath) = Just $ ProofStep Evident IdentityPath
applyApId (Ap (IdentityFunction _) p) = Just $ ProofStep Evident p
applyApId _ = Nothing

nilConcatOne :: FunctionRewrite
nilConcatOne ((FunctionApplication (Literal (Symbol "_++_")) [Nil])) = Just (IdentityFunction Unknown, Evident)
nilConcatOne _ = Nothing

applyNilConcatOne :: RewriteRuleDefinition
applyNilConcatOne = rewriteFunction nilConcatOne

applyApFusion :: RewriteRuleDefinition
applyApFusion (Composition (Ap f p) (Ap f' p')) =
  if f == f'
    then Just $ ProofStep (Justification (ApFusionRule f p p')) (Ap f (Composition p p'))
    else Nothing
applyApFusion _ = Nothing

concat' :: Expression -> Expression -> Expression
concat' xs ys = FunctionApplication (Literal (Symbol "_++_")) [xs, ys]

-- TODO: Perhaps generalise these
applyNilConcatTwo :: Expression -> Maybe ProofStep
applyNilConcatTwo (FunctionApplication (Literal (Symbol "_++_")) [Nil, xs]) = Just $ ProofStep Evident xs
applyNilConcatTwo _ = Nothing

applyConsConcat :: Expression -> Maybe ProofStep
applyConsConcat (FunctionApplication (Literal (Symbol "_++_")) [Cons x xs, ys]) = Just $ ProofStep Evident (Cons x (concat' xs ys))
applyConsConcat _ = Nothing

applyConcatAssocNil :: Expression -> Maybe ProofStep
applyConcatAssocNil (FunctionApplication (Literal (Symbol "++-assoc")) [Nil, ys, zs]) = Just $ ProofStep Evident IdentityPath
applyConcatAssocNil _ = Nothing

x_ :: Symbol
x_ = Identifier 0

x_' :: Expression
x_' = Literal x_

concatAssoc' :: Expression -> Expression -> Expression -> Expression
concatAssoc' xs ys zs = FunctionApplication (Literal (Symbol "++-assoc")) [xs, ys, zs]

consOne' :: Expression -> Expression
consOne' x = FunctionApplication (Literal (Symbol "_∷_")) [x]

consTwo' :: Expression -> Expression -> Expression
consTwo' x y = FunctionApplication (Literal (Symbol "_∷_")) [x, y]

applyConcatAssocCons :: Expression -> Maybe ProofStep
applyConcatAssocCons
  ( FunctionApplication
      (Literal (Symbol "++-assoc"))
      [Cons x xs, ys, zs]
    ) =
    Just $
      ProofStep
        (Justification NilConcatTwoRule)
        (Ap (Lambda x_ (consTwo' x x_')) (concatAssoc' xs ys zs))
applyConcatAssocCons _ = Nothing
