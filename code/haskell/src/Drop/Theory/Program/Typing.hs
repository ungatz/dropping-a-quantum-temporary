-- Drop.Theory.Program.Typing: the typing rules of the calculus, as a decision procedure.
--
-- Question: Is a term well typed in a context, and at which type?
-- Answer:   typeOf g e decides the judgement g |- e : A, one case for each form of term, with
--           every side condition written out. A context is exact: a term must name every register
--           of its context, so a register that is neither returned nor dropped is refused
--           (LeftoverNames) and there is no implicit weakening. Drop is the only way to discard a
--           temporary. checkGate tests a gate's matrix in this order: the declared dimensions,
--           squareness, the width of every row, then unitarity. A program is typed when it is
--           `let t = new i0 in e` and ends at its visible type (checkProgram). Contexts are
--           association lists in the tensor order.
-- Paper:    sec:lang:statics (the rules themselves are in app:core-rules).
-- Shapes:   Ctx            a list of (name, register type) in tensor order.
--           TypeError      one constructor for each way a term is refused.
--           TypedProgram   a checked program with its temporary's name, dimension and allocation
--                          index, the visible dimension, and the body of the outermost new.

module Drop.Theory.Program.Typing
  ( -- * Contexts
    Ctx
  , ctxLookup, ctxNames, ctxDims, ctxPos, ctxRemove, ctxRename, ctxExtend
    -- * Errors
  , TypeError(..)
    -- * The judgement
  , typeOf
  , checkGate
    -- * Programs
  , TypedProgram(..)
  , checkProgram
  ) where

import Data.List (sort)

import Drop.Theory.Algebra.Linear
import Drop.Theory.Program.Syntax

-- | A context: a finite partial map from names to register types, represented
-- in tensor order.
type Ctx = [(Name, RegTy)]

-- A context lists the registers in tensor order.
-- >>> [("v", Vis 2), ("t", Tmp 3)] :: Ctx
-- [("v",vis[2]),("t",tmp[3])]

ctxLookup :: Name -> Ctx -> Maybe RegTy
ctxLookup = lookup

-- >>> ctxLookup "t" [("v", Vis 2), ("t", Tmp 3)]
-- Just tmp[3]
-- >>> ctxLookup "x" [("v", Vis 2), ("t", Tmp 3)]
-- Nothing

ctxNames :: Ctx -> [Name]
ctxNames = map fst

-- >>> ctxNames [("v", Vis 2), ("t", Tmp 3)]
-- ["v","t"]

ctxDims :: Ctx -> [Int]
ctxDims = map (regDim . snd)

-- >>> ctxDims [("v", Vis 2), ("t", Tmp 3)]
-- [2,3]

-- | The position of a name in the tensor order.
ctxPos :: Name -> Ctx -> Maybe Int
ctxPos x g = go 0 g
  where
    go _ [] = Nothing
    go i ((y,_):rest) | x == y    = Just i
                      | otherwise = go (i+1) rest

-- >>> ctxPos "t" [("v", Vis 2), ("t", Tmp 3)]
-- Just 1
-- >>> ctxPos "x" [("v", Vis 2), ("t", Tmp 3)]
-- Nothing

ctxRemove :: Name -> Ctx -> Ctx
ctxRemove x = filter ((/= x) . fst)

-- >>> ctxRemove "v" [("v", Vis 2), ("t", Tmp 3)]
-- [("t",tmp[3])]
-- >>> ctxRemove "x" [("v", Vis 2)]
-- [("v",vis[2])]

-- | Rename in place, keeping the tensor position.
ctxRename :: Name -> Name -> RegTy -> Ctx -> Ctx
ctxRename old new q = map (\(y,r) -> if y == old then (new,q) else (y,r))

-- Renaming keeps the position in the tensor order.
-- >>> ctxRename "v" "w" (Vis 2) [("v", Vis 2), ("t", Tmp 3)]
-- [("w",vis[2]),("t",tmp[3])]

-- | Extend on the right; the fresh register is least significant.
ctxExtend :: Name -> RegTy -> Ctx -> Ctx
ctxExtend x q g = g ++ [(x,q)]

-- A fresh register goes on the right, least significant.
-- >>> ctxExtend "t" (Tmp 3) [("v", Vis 2)]
-- [("v",vis[2]),("t",tmp[3])]

-- Errors

data TypeError
  = LeftoverNames [Name]
      -- ^ The context has names the term never consumes.  This is the
      -- exact-context discipline biting: implicit weakening is not admissible.
  | UnboundName Name
  | NotATemporary Name RegTy
  | NotVisible Name RegTy
  | DuplicateName Name
  | AllocInBody
      -- ^ @allocFree@ failed: a second allocation inside an allocation body.
  | BadAllocIndex Int Int
  | GateShapeMismatch String Int Int Int Int
      -- ^ gate label, expected tmp dim, expected vis dim, actual, actual
  | GateNotSquare String Int Int
  | GateNotRectangular String Int [Int]
      -- ^ Gate label, the side @n@ it claims, and the actual width of every
      -- row.  A gate matrix is a bare list of lists, so the row count and the
      -- first row's width do not between them rule out a ragged matrix.
  | GateNotUnitary String
  | TemporaryIsVisible Name
  | GateOutputsCoincide Name
      -- ^ The @Gate@ rule binds a pattern @(t',v')@.  Pattern linearity
      -- demands @t' /= v'@, exactly as @Pair@ demands @v1 /= v2@; one name
      -- cannot stand for two registers.  Reusing a /consumed input/ name is a
      -- different thing and stays legal: ordinary shadowing.
  | BadRegisterDimension Name Int
      -- ^ A register dimension must be at least one.  @vis[0]@ is not an empty
      -- register, it is not a register.
  | ProgramMustAllocate
  | ProgramResultType Ty Ty
  deriving (Eq)

-- Each refusal prints as the sentence that explains it.
-- >>> UnboundName "x"
-- unbound register name "x"
-- >>> BadAllocIndex 2 2
-- allocation index 2 is not in [0..1]
-- >>> DuplicateName "t"
-- the name "t" is already bound; displayed names must be fresh
-- >>> NotATemporary "v" (Vis 2)
-- "v" has type vis[2], not tmp[_]
-- >>> ProgramMustAllocate
-- a program must be `let t = new i0 in e`
-- >>> LeftoverNames ["t"]
-- the context still holds ["t"] when the term ends; the Var rule has an exact context, so there is no implicit weakening to discard them

instance Show TypeError where
  show (LeftoverNames xs) =
    "the context still holds " ++ show xs ++ " when the term ends; the Var rule "
    ++ "has an exact context, so there is no implicit weakening to discard them"
  show (UnboundName x)      = "unbound register name " ++ show x
  show (NotATemporary x q)  = show x ++ " has type " ++ show q ++ ", not tmp[_]"
  show (NotVisible x q)     = show x ++ " has type " ++ show q ++ ", not vis[_]"
  show (DuplicateName x)    = "the name " ++ show x ++ " is already bound; "
                              ++ "displayed names must be fresh"
  show AllocInBody          = "allocFree failed: the body of an allocation "
                              ++ "allocates again, so this program would have "
                              ++ "more than one temporary scope"
  show (BadAllocIndex i d)  = "allocation index " ++ show i
                              ++ " is not in [0.." ++ show (d-1) ++ "]"
  show (GateShapeMismatch nm ed em ad am) =
    "gate " ++ nm ++ " is declared on tmp[" ++ show ad ++ "] (x) vis[" ++ show am
    ++ "] but is applied to tmp[" ++ show ed ++ "] (x) vis[" ++ show em ++ "]"
  show (GateNotSquare nm r c) =
    "gate " ++ nm ++ " has a " ++ show r ++ "x" ++ show c ++ " matrix, not square"
  show (GateNotRectangular nm n ws) =
    "gate " ++ nm ++ " claims to be " ++ show n ++ "x" ++ show n
    ++ " but its rows have widths " ++ show ws
    ++ "; a gate matrix is a list of lists here, so every row is checked"
  show (GateNotUnitary nm) =
    "gate " ++ nm ++ " is not unitary; the Gate rule's premise "
    ++ "U^dagger U = U U^dagger = I fails exactly"
  show (GateOutputsCoincide x) =
    "the Gate rule binds the pattern (t',v') and needs t' /= v', but both "
    ++ "output binders are " ++ show x ++ "; this is pattern linearity, the "
    ++ "same premise Pair carries as v1 /= v2"
  show (BadRegisterDimension x n) =
    "register " ++ show x ++ " is declared with dimension " ++ show n
    ++ "; a register dimension must be at least 1"
  show (TemporaryIsVisible x) =
    "the Gate rule needs t /= v, but both arguments are " ++ show x
  show ProgramMustAllocate =
    "a program must be `let t = new i0 in e`"
  show (ProgramResultType want got) =
    "a program must end at the visible type " ++ show want ++ ", not " ++ show got

-- >>> show (UnboundName "x")
-- "unbound register name \"x\""
-- >>> show (ProgramMustAllocate)
-- "a program must be `let t = new i0 in e`"

-- The judgement

-- | @typeOf g e@ decides @g |- e : A@.
--
-- Read against the rules:
--
-- > ------------------ Var          ------------------------------- Pair
-- >   v:A |- v : A                    v1:A, v2:B |- <v1,v2> : A (x) B
-- >
-- >   t not in dom(G)   i0 in [d]   allocFree(e)   G, t:tmp[d] |- e : C
-- >  -------------------------------------------------------------------- New
-- >              G |- let t = new i0 in e : C
-- >
-- >   t /= v   U : H_d (x) H_m -> H_d (x) H_m   U^t U = U U^t = I
-- >   G, t':tmp[d], v':vis[m] |- e : C
-- >  ---------------------------------------------------------------- Gate
-- >   G, t:tmp[d], v:vis[m] |- let (t',v') = U(t,v) in e : C
-- >
-- >         G |- e : C
-- >  -------------------------- Drop
-- >   G, t:tmp[d] |- drop t; e : C
typeOf :: Ctx -> Term -> Either TypeError Ty

typeOf g (Ret v) =
  case ctxLookup v g of
    Nothing -> Left (UnboundName v)
    Just q
      | length g /= 1 -> Left (LeftoverNames (filter (/= v) (ctxNames g)))
      | otherwise     -> Right (TyReg q)

typeOf g (Pair v1 v2)
  | v1 == v2 = Left (DuplicateName v1)
  | otherwise =
      case (ctxLookup v1 g, ctxLookup v2 g) of
        (Nothing, _) -> Left (UnboundName v1)
        (_, Nothing) -> Left (UnboundName v2)
        (Just a, Just b)
          | sort (ctxNames g) /= sort [v1,v2] ->
              Left (LeftoverNames (filter (`notElem` [v1,v2]) (ctxNames g)))
          | otherwise -> Right (TyPair (TyReg a) (TyReg b))

typeOf g (New t d i0 e)
  | d < 1                      = Left (BadRegisterDimension t d)
  | t `elem` ctxNames g        = Left (DuplicateName t)
  | i0 < 0 || i0 >= d          = Left (BadAllocIndex i0 d)
  | not (allocFree e)          = Left AllocInBody
  | otherwise                  = typeOf (ctxExtend t (Tmp d) g) e

typeOf g (Act (t',v') u (t,v) e)
  | t == v = Left (TemporaryIsVisible t)
  | otherwise =
      case (ctxLookup t g, ctxLookup v g) of
        (Nothing, _) -> Left (UnboundName t)
        (_, Nothing) -> Left (UnboundName v)
        (Just qt, Just qv) -> do
          d <- case qt of Tmp d' -> Right d'; _ -> Left (NotATemporary t qt)
          m <- case qv of Vis m' -> Right m'; _ -> Left (NotVisible v qv)
          if t' == v' then Left (GateOutputsCoincide t') else Right ()
          checkGate u d m
          let g1 = ctxRename t t' (Tmp d) g
              g2 = ctxRename v v' (Vis m) g1
          mapM_ (\x -> if x `elem` ctxNames (ctxRemove t (ctxRemove v g))
                         then Left (DuplicateName x) else Right ())
                [t', v']
          typeOf g2 e

typeOf g (Drop t e) =
  case ctxLookup t g of
    Nothing        -> Left (UnboundName t)
    Just q@(Vis _) -> Left (NotATemporary t q)
    Just (Tmp _)   -> typeOf (ctxRemove t g) e

-- Var: a value must use the whole context; there is no implicit weakening.
-- >>> :m + Drop.Theory.Corpus.Examples Drop.Theory.Program.Gates Drop.Theory.Algebra.Scalar
-- >>> typeOf [("v", Vis 2)] (Ret "v")
-- Right vis[2]
-- >>> typeOf [("v", Vis 2), ("t", Tmp 2)] (Ret "v")
-- Left the context still holds ["t"] when the term ends; the Var rule has an exact context, so there is no implicit weakening to discard them
-- >>> typeOf [("v", Vis 2)] (Ret "w")
-- Left unbound register name "w"
-- >>> typeOf [("a", Vis 2), ("b", Tmp 3)] (Pair "a" "b")
-- Right (vis[2] (x) tmp[3])
-- >>> typeOf [("a", Vis 2)] (Pair "a" "a")
-- Left the name "a" is already bound; displayed names must be fresh
-- >>> typeOf [("v", Vis 2)] (New "t" 2 5 (Ret "v"))
-- Left allocation index 5 is not in [0..1]
-- >>> typeOf [("v", Vis 2)] (New "t" 2 0 (Ret "v"))
-- Left the context still holds ["t"] when the term ends; the Var rule has an exact context, so there is no implicit weakening to discard them
-- >>> typeOf [("v", Vis 2), ("t", Tmp 2)] (Drop "v" (Ret "t"))
-- Left "v" has type vis[2], not tmp[_]
-- >>> typeOf [("v", Vis 2)] (progTerm spreadAndPark)
-- Right vis[2]
-- >>> typeOf [("v", Vis 2)] (progTerm spreadAndRead)
-- Right vis[2]

-- | The @Gate@ rule's premises about the matrix, all three of them.
checkGate :: Gate -> Int -> Int -> Either TypeError ()
checkGate u d m
  | gateTmpDim u /= d || gateVisDim u /= m =
      Left (GateShapeMismatch (show u) d m (gateTmpDim u) (gateVisDim u))
  | matRows (gateMat u) /= n || matCols (gateMat u) /= n =
      Left (GateNotSquare (show u) (matRows (gateMat u)) (matCols (gateMat u)))
  -- Rectangularity before unitarity, and it is not implied by the clause
  -- above: matCols reads the first row only, so without this a ragged matrix
  -- would reach matIsUnitary and the diagnostic would blame the wrong premise.
  | not (matIsRectangular n (gateMat u)) =
      Left (GateNotRectangular (show u) n (matRowWidths (gateMat u)))
  | not (matIsUnitary (gateMat u)) = Left (GateNotUnitary (show u))
  | otherwise = Right ()
  where n = d * m

-- The four premises, in order: dimensions, squareness, row widths, unitarity.
-- >>> checkGate (gHt 2) 2 2
-- Right ()
-- >>> checkGate (gHt 2) 2 3
-- Left gate H is declared on tmp[2] (x) vis[2] but is applied to tmp[2] (x) vis[3]
-- >>> checkGate (joint "tall" 2 1 [[kone], [kone]]) 2 1
-- Left gate tall has a 2x1 matrix, not square
-- >>> checkGate (joint "ragged" 2 1 [[kone, kzero], [kzero]]) 2 1
-- Left gate ragged claims to be 2x2 but its rows have widths [2,1]; a gate matrix is a list of lists here, so every row is checked
-- >>> checkGate (joint "ones" 2 1 [[kone, kone], [kone, kone]]) 2 1
-- Left gate ones is not unitary; the Gate rule's premise U^dagger U = U U^dagger = I fails exactly

-- Programs

-- | The result of checking a program: everything downstream needs the
-- temporary's name, dimension and allocation index, and they are only known
-- after typing.
data TypedProgram = TypedProgram
  { tpProgram :: Program
  , tpTmpName :: Name
  , tpTmpDim  :: Int     -- ^ @d@
  , tpAlloc   :: Int     -- ^ @i0@
  , tpVisDim  :: Int     -- ^ @m@
  , tpBody    :: Term    -- ^ the body of the outermost @new@
  }

-- A checked program keeps what typing found: the temporary's name, dimension and allocation index.
-- >>> fmap tpTmpName (checkProgram spreadAndPark)
-- Right "t"
-- >>> fmap (\tp -> (tpTmpDim tp, tpAlloc tp, tpVisDim tp)) (checkProgram tiltThenRead)
-- Right (3,0,3)
-- >>> fmap (length . gatesIn . tpBody) (checkProgram spreadAndRead)
-- Right 2

-- | A program is typed when
--
-- > v : vis[m] |- let t = new i0 in e : vis[m].
checkProgram :: Program -> Either TypeError TypedProgram
checkProgram p
  -- The visible dimension arrives from outside the term and nothing else
  -- validates it.  @vis[0]@ is not an empty register but no register at all,
  -- and the denotation's shape, the criterion's rank and the continuation
  -- family are all meaningless without this check.
  | progVisDim p < 1 =
      Left (BadRegisterDimension (progVis p) (progVisDim p))
checkProgram p =
  case progTerm p of
    New t d i0 body -> do
      let g0  = [(progVis p, Vis (progVisDim p))]
          out = TyReg (Vis (progVisDim p))
      ty <- typeOf g0 (New t d i0 body)
      if ty /= out
        then Left (ProgramResultType out ty)
        else Right TypedProgram { tpProgram = p
                                , tpTmpName = t
                                , tpTmpDim  = d
                                , tpAlloc   = i0
                                , tpVisDim  = progVisDim p
                                , tpBody    = body }
    _ -> Left ProgramMustAllocate

-- A program is `let t = new i0 in e` ending at its visible type.
-- >>> either show (const "typed") (checkProgram spreadAndPark)
-- "typed"
-- >>> either show (const "typed") (checkProgram (Program "p" "v" 2 (Ret "v")))
-- "a program must be `let t = new i0 in e`"
-- >>> either show (const "typed") (checkProgram (Program "p" "v" 0 (Ret "v")))
-- "register \"v\" is declared with dimension 0; a register dimension must be at least 1"
-- >>> either show (const "typed") (checkProgram (Program "p" "v" 2 (New "t" 2 0 (Pair "t" "v"))))
-- "a program must end at the visible type vis[2], not (tmp[2] (x) vis[2])"
-- >>> map (either show (const "typed") . checkProgram . snd) catalogue
-- ["typed","typed","typed","typed","typed","typed","typed","typed","typed","typed","typed","typed","typed","typed","typed","typed","typed"]
