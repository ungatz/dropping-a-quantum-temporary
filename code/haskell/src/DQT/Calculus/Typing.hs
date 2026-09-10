-- |
-- Module      : DQT.Calculus.Typing
--
-- The typing rules as a decision procedure, with every side
-- condition written out, including the exact context in @Var@ that forbids
-- hidden weakening.  Contexts are association lists in the tensor order.
module DQT.Calculus.Typing
  ( -- * Contexts
    Ctx
  , ctxLookup, ctxNames, ctxDims, ctxPos, ctxRemove, ctxRebind, ctxExtend
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

import DQT.Algebra.Linear
import DQT.Calculus.Syntax

-- | A context: a finite partial map from names to register types, represented
-- in tensor order.
type Ctx = [(Name, RegTy)]

ctxLookup :: Name -> Ctx -> Maybe RegTy
ctxLookup = lookup

ctxNames :: Ctx -> [Name]
ctxNames = map fst

ctxDims :: Ctx -> [Int]
ctxDims = map (regDim . snd)

-- | The position of a name in the tensor order.
ctxPos :: Name -> Ctx -> Maybe Int
ctxPos x g = go 0 g
  where
    go _ [] = Nothing
    go i ((y,_):rest) | x == y    = Just i
                      | otherwise = go (i+1) rest

ctxRemove :: Name -> Ctx -> Ctx
ctxRemove x = filter ((/= x) . fst)

-- | Rebind the @Gate@ rule's two outputs, each keeping its tensor position.
--
-- Simultaneous, and it has to be.  Renaming @t@ and then @v@ lets the first
-- rename produce an entry named @v@ that the second then catches, so
-- @let (v,t) = U(t,v)@ -- the outputs taking the consumed inputs' names, which
-- is the ordinary shadowing 'GateOutputsCoincide' documents as legal -- ends
-- with two entries under one name and gives the temporary the visible
-- register's type.  There is no single-name rename here on purpose: @Gate@ is
-- the only rule that renames, and it always renames a pair.
ctxRebind :: (Name, Name, RegTy) -> (Name, Name, RegTy) -> Ctx -> Ctx
ctxRebind (t, t', qt) (v, v', qv) = map step
  where
    step (y, r) | y == t    = (t', qt)
                | y == v    = (v', qv)
                | otherwise = (y, r)

-- | Extend on the right; the fresh register is least significant.
ctxExtend :: Name -> RegTy -> Ctx -> Ctx
ctxExtend x q g = g ++ [(x,q)]

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
          let g2 = ctxRebind (t, t', Tmp d) (v, v', Vis m) g
          mapM_ (\x -> if x `elem` ctxNames (ctxRemove t (ctxRemove v g))
                         then Left (DuplicateName x) else Right ())
                [t', v']
          typeOf g2 e

typeOf g (Drop t e) =
  case ctxLookup t g of
    Nothing        -> Left (UnboundName t)
    Just q@(Vis _) -> Left (NotATemporary t q)
    Just (Tmp _)   -> typeOf (ctxRemove t g) e

-- | The @Gate@ rule's premises about the matrix, all three of them.
--
-- Exported because "DQT.Lifted" has the same @Gate@ rule and must not have a
-- second copy of it: a premise checked in two places is a premise that can
-- drift in one.
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
