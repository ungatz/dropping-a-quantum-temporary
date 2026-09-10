-- |
-- Module      : DQT.Calculus.Elaborate
--
-- The retaining denotation: a total function from typing derivations to
-- linear maps, by structural recursion. @Drop@ cannot denote an identity,
-- so the denotation carries the dropped factors along in the result type.
module DQT.Calculus.Elaborate
  ( -- * The denotation
    Denotation(..)
  , denote
    -- * Programs
  , coreMap
  , droppedDims
    -- * Cross-check against the operational semantics
  , agreesWithMachine
  ) where

import DQT.Algebra.Linear
import DQT.Calculus.Machine (runTerm)
import DQT.Calculus.Syntax
import DQT.Calculus.Typing

-- | @[[e]] : [[G]] -> H_{delta} (x) [[C]]@, together with @delta@ and the
-- codomain type.
data Denotation = Denotation
  { denDropped :: [Int]   -- ^ @delta(e)@: the dropped dimensions, in drop order
  , denResult  :: Ty      -- ^ @C@
  , denMatrix  :: Mat     -- ^ rows @product delta * tyDim C@, columns @product (dims G)@
  }

-- | The retaining denotation, by structural recursion on the term, following
-- the typing rules exactly.  Fails on an ill-typed term with the type error
-- that 'typeOf' would give.
denote :: Ctx -> Term -> Either TypeError Denotation

denote g e@(Ret _) = do
  ty <- typeOf g e
  pure Denotation { denDropped = []
                  , denResult  = ty
                  , denMatrix  = matId (dimProduct (ctxDims g)) }

denote g e@(Pair v1 v2) = do
  ty <- typeOf g e
  -- The context may hold the two names in either order; the result type puts
  -- v1 first, so the denotation is the reordering that does the same.
  let dims  = ctxDims g
      order = [ pos v1, pos v2 ]
      pos x = maybe (error "DQT.Calculus.Elaborate.denote: Pair name absent") id (ctxPos x g)
  pure Denotation { denDropped = []
                  , denResult  = ty
                  , denMatrix  = reorder dims order }

denote g (New t d i0 e) = do
  _ <- typeOf g (New t d i0 e)          -- re-run the rule's side conditions
  let g'   = ctxExtend t (Tmp d) g
      n    = dimProduct (ctxDims g)
      -- the inclusion  [[G]] -> [[G]] (x) H_d,  x |-> x (x) e_{i0}
      incl = kron (matId n) (matFromCols [vbasis d i0])
  inner <- denote g' e
  pure inner { denMatrix = matMul (denMatrix inner) incl }

denote g (Act (t',v') u (t,v) e) = do
  _ <- typeOf g (Act (t',v') u (t,v) e)
  let dims = ctxDims g
      pt   = must (ctxPos t g)
      pv   = must (ctxPos v g)
      ug   = applyGateAt dims (gateMat u) [pt, pv]
      d    = dims !! pt
      m    = dims !! pv
      g2   = ctxRebind (t, t', Tmp d) (v, v', Vis m) g
  inner <- denote g2 e
  pure inner { denMatrix = matMul (denMatrix inner) ug }
  where must = maybe (error "DQT.Calculus.Elaborate.denote: Act name absent") id

denote g (Drop t e) = do
  _ <- typeOf g (Drop t e)
  let dims = ctxDims g
      p    = maybe (error "DQT.Calculus.Elaborate.denote: Drop name absent") id (ctxPos t g)
      d    = dims !! p
      g'   = ctxRemove t g
      -- [[G]] -> H_d (x) [[G']]
      move = permuteToFront dims p
  inner <- denote g' e
  pure Denotation
    { denDropped = d : denDropped inner
    , denResult  = denResult inner
    , denMatrix  = matMul (kron (matId d) (denMatrix inner)) move }

-- | @delta@ for a program: the dimensions of the temporaries it drops.
droppedDims :: TypedProgram -> [Int]
droppedDims tp =
  case denote [(progVis (tpProgram tp), Vis (tpVisDim tp))] (progTerm (tpProgram tp)) of
    Right dn -> denDropped dn
    Left err -> error ("DQT.Calculus.Elaborate.droppedDims: " ++ show err)

-- | The denotation @K_P : H_m -> H_d (x) H_m@ of a typed program.  Its rows are
-- indexed by a pair (temporary basis state, visible basis state) and its columns by a
-- visible basis state, in the mixed-radix convention of "DQT.Algebra.Linear".
coreMap :: TypedProgram -> Mat
coreMap tp =
  case denote g0 (progTerm (tpProgram tp)) of
    Left err -> error ("DQT.Calculus.Elaborate.coreMap: " ++ show err)
    Right dn
      | denDropped dn /= [tpTmpDim tp] ->
          error ("DQT.Calculus.Elaborate.coreMap: expected exactly one drop of dimension "
                 ++ show (tpTmpDim tp) ++ ", got " ++ show (denDropped dn))
      | otherwise -> denMatrix dn
  where g0 = [(progVis (tpProgram tp), Vis (tpVisDim tp))]

-- | Do the compositional denotation and the operational machine agree?
--
-- They are two definitions of the same object, one by recursion on the typing
-- derivation and one by stepping a configuration, so their agreement is
-- adequacy in miniature and is checked rather than asserted.
agreesWithMachine :: TypedProgram -> Bool
agreesWithMachine tp =
  and [ matVec k (vbasis m j) == runTerm tp (vbasis m j) | j <- [0 .. m - 1] ]
  where k = coreMap tp
        m = tpVisDim tp
