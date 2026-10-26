-- Drop.Theory.Program.Elaborate: the linear map a term denotes.
--
-- Question: Which linear map does a typed term denote, and does it agree with the machine?
-- Answer:   denote follows the typing rules by recursion on the term. Ret is the identity on the
--           context, Pair reorders the two named registers, New composes with the inclusion
--           x to x (x) e_i0, an Act composes with its gate placed on the two registers, and Drop
--           moves the dropped register to the front (permuteToFront) and keeps it as an output
--           factor, so the dimensions dropped, in drop order, come first in the output. An
--           ill-typed term gives the type error. The denotation of a program is coreMap: a matrix
--           whose columns are the visible basis states and whose rows are the pairs (temporary,
--           visible). agreesWithMachine compares it with a run of Drop.Theory.Program.Machine on
--           each visible basis state.
-- Paper:    sec:lang:denotation.
-- Shapes:   Denotation   the dropped dimensions, the result type and the matrix.

module Drop.Theory.Program.Elaborate
  ( -- * The denotation
    Denotation(..)
  , denote
    -- * Programs
  , coreMap
  , droppedDims
    -- * Cross-check against the operational semantics
  , agreesWithMachine
  ) where

import Drop.Theory.Algebra.Linear
import Drop.Theory.Program.Machine (runTerm)
import Drop.Theory.Program.Syntax
import Drop.Theory.Program.Typing

-- | @[[e]] : [[G]] -> H_{delta} (x) [[C]]@, together with @delta@ and the
-- codomain type.
data Denotation = Denotation
  { denDropped :: [Int]   -- ^ @delta(e)@: the dropped dimensions, in drop order
  , denResult  :: Ty      -- ^ @C@
  , denMatrix  :: Mat     -- ^ rows @product delta * tyDim C@, columns @product (dims G)@
  }

-- Spread and park: one drop of dimension 2, and the result type is the visible register.
-- >>> :m + Drop.Theory.Corpus.Examples
-- >>> let Right dn = denote [("v", Vis 2)] (progTerm spreadAndPark)
-- >>> (denDropped dn, denResult dn)
-- ([2],vis[2])
-- >>> denMatrix dn
-- [[sqrt2/2,0],[0,sqrt2/2],[sqrt2/2,0],[0,sqrt2/2]]

-- | The retaining denotation, by structural recursion on the term, following
-- the typing rules exactly.  An ill-typed term gives the type error that
-- 'typeOf' would give.
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
      -- impossible: typeOf accepted the term, so both names are in the context
      pos x = maybe (error "Drop.Theory.Program.Elaborate.denote: Pair name absent") id (ctxPos x g)
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
      -- impossible: pt is a position in the context, which has one dimension for each name
      d    = dims !! pt
      -- impossible: as above, for pv
      m    = dims !! pv
      g2   = ctxRename v v' (Vis m) (ctxRename t t' (Tmp d) g)
  inner <- denote g2 e
  pure inner { denMatrix = matMul (denMatrix inner) ug }
  -- impossible: typeOf accepted the term, so both names are in the context
  where must = maybe (error "Drop.Theory.Program.Elaborate.denote: Act name absent") id

denote g (Drop t e) = do
  _ <- typeOf g (Drop t e)
  let dims = ctxDims g
      -- impossible: typeOf accepted the term, so the name is in the context
      p    = maybe (error "Drop.Theory.Program.Elaborate.denote: Drop name absent") id (ctxPos t g)
      -- impossible: p is a position in the context
      d    = dims !! p
      g'   = ctxRemove t g
      -- [[G]] -> H_d (x) [[G']]
      move = permuteToFront dims p
  inner <- denote g' e
  pure Denotation
    { denDropped = d : denDropped inner
    , denResult  = denResult inner
    , denMatrix  = matMul (kron (matId d) (denMatrix inner)) move }

-- Ret is the identity; Pair reorders; a context that is not used up is refused as typeOf refuses it.
-- >>> fmap denMatrix (denote [("v", Vis 2)] (Ret "v"))
-- Right [[1,0],[0,1]]
-- >>> fmap denMatrix (denote [("a", Vis 2), ("b", Vis 2)] (Pair "b" "a"))
-- Right [[1,0,0,0],[0,0,1,0],[0,1,0,0],[0,0,0,1]]
-- >>> fmap denDropped (denote [("v", Vis 2)] (progTerm spreadAndRead))
-- Right [2]
-- >>> fmap denResult (denote [("v", Vis 2)] (progTerm spreadAndRead))
-- Right vis[2]
-- >>> either show (const "denoted") (denote [("v", Vis 2), ("w", Vis 2)] (Ret "v"))
-- "the context still holds [\"w\"] when the term ends; the Var rule has an exact context, so there is no implicit weakening to discard them"

-- | @delta@ for a program: the dimensions of the temporaries it drops.
droppedDims :: TypedProgram -> [Int]
droppedDims tp =
  case denote [(progVis (tpProgram tp), Vis (tpVisDim tp))] (progTerm (tpProgram tp)) of
    Right dn -> denDropped dn
    -- refusal: a program that was not type checked
    Left err -> error ("Drop.Theory.Program.Elaborate.droppedDims: " ++ show err)

-- >>> fmap droppedDims (checkProgram twoGateSilq)
-- Right [2]
-- >>> fmap droppedDims (checkProgram tiltThenRead)
-- Right [3]

-- | The denotation @K_P : H_m -> H_d (x) H_m@ of a typed program.  Its rows are
-- indexed by a pair (temporary basis state, visible basis state) and its columns by a
-- visible basis state, in the mixed-radix convention of "Drop.Theory.Algebra.Linear".
coreMap :: TypedProgram -> Mat
coreMap tp =
  case denote g0 (progTerm (tpProgram tp)) of
    -- refusal: a program that was not type checked
    Left err -> error ("Drop.Theory.Program.Elaborate.coreMap: " ++ show err)
    Right dn
      | denDropped dn /= [tpTmpDim tp] ->
          -- impossible: a typed program allocates one temporary and drops it once
          error ("Drop.Theory.Program.Elaborate.coreMap: expected exactly one drop of dimension "
                 ++ show (tpTmpDim tp) ++ ", got " ++ show (denDropped dn))
      | otherwise -> denMatrix dn
  where g0 = [(progVis (tpProgram tp), Vis (tpVisDim tp))]

-- The map of spread and read on the input |0>: the correlated pair (|0,0> + |1,1>)/sqrt2, dropped block first.
-- >>> fmap (\tp -> matColumn (coreMap tp) 0) (checkProgram spreadAndRead)
-- Right [sqrt2/2,0,0,sqrt2/2]
-- >>> fmap (\tp -> (matRows (coreMap tp), matCols (coreMap tp))) (checkProgram spreadAndRead)
-- Right (4,2)
-- >>> fmap coreMap (checkProgram twoGateSilq)
-- Right [[1,0],[0,1],[0,0],[0,0]]

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

-- The compositional map and the machine agree on each program of the catalogue.
-- >>> fmap agreesWithMachine (checkProgram spreadAndRead)
-- Right True
-- >>> and [ agreesWithMachine tp | (_, p) <- catalogue, Right tp <- [checkProgram p] ]
-- True
-- >>> length [ () | (_, p) <- catalogue, Right _ <- [checkProgram p] ]
-- 17
