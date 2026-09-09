-- |
-- Module      : DQT.Many.Release
--
-- What the next borrower receives: a released temporary carries a
-- certificate @Released d [g]@, a ray rather than a state, since it is
-- determined only up to @(lambda g, lambda^{-1} W)@.
module DQT.Many.Release
  ( -- * The release certificate
    Released(..)
  , Pool
  , cleanCertificate
  , isClean
    -- * The two pool operations
  , borrow
  , release
    -- * The restoration plan
  , restore
  , restoreCost
    -- * The weaker rule, and the size of the gap
  , restoredToAllocation
  , restorationRuleIsSufficient
  , restorationRuleIsNotNecessary
  , restorationGap
  , poolReport
  ) where

import Data.List (intercalate)

import DQT.Criterion (Verdict(..), parkedLine, verdict)
import DQT.Pretty (wrapAt)
import DQT.Corpus.Examples (catalogue)
import DQT.Algebra.Linear (Mat, Vec, matIsIdentity, vbasis, vnorm2)
import DQT.Algebra.Scalar (kdiv, ksqrtReal)
import DQT.Criterion.Split (canonicalLine, lineEqual)
import DQT.Calculus.Typing (TypedProgram(..), checkProgram)
import DQT.Criterion.Witness (Reason(..), householder)

-- The certificate

-- | A released temporary: its dimension, and the ray it rests on.  The vector is
-- stored in the canonical representative of its ray, so equality of
-- certificates is equality of the thing the certificate is about.
data Released = Released
  { releasedDim :: Int
  , releasedRay :: Vec
  } deriving (Eq)

instance Show Released where
  show (Released d g) = "Q" ++ show d ++ " resting on " ++ show g

-- | The pool is a bag: order does not matter, and two temporaries resting on
-- the same ray are two temporaries.
type Pool = [Released]

-- | The certificate a freshly allocated temporary would carry if it were
-- handed straight back: it rests on the allocation ray.
cleanCertificate :: Int -> Int -> Released
cleanCertificate d i0 = Released d (canonicalLine (vbasis d i0))

-- | Does this temporary rest where a borrower allocating at @i0@ expects?
isClean :: Int -> Released -> Bool
isClean i0 c = lineEqual (releasedRay c) (vbasis (releasedDim c) i0)

-- The two pool operations

-- | Take a temporary of dimension @d@ out of the pool.  Returns the ray it
-- arrives on together with the remaining pool; a borrower that needs the
-- allocation ray and is handed something else must 'restore' it first.
borrow :: Int -> Pool -> Maybe (Vec, Pool)
borrow d pool = case break ((== d) . releasedDim) pool of
  (before, c : after) -> Just (releasedRay c, before ++ after)
  _                   -> Nothing

-- | Give a temporary up. The certificate is determined by the program,
-- not chosen: it records the ray the drop leaves the temporary on, and
-- exists exactly when the drop is safe.
--
-- A refused drop yields no certificate: the temporary cannot return to
-- the pool.  Reinitialising it is NOT a repair -- a reset is a discard
-- followed by a preparation, and the discard is exactly what the criterion
-- refused, so the visible channel is damaged either way.  The register stays
-- live until the program restores it, or the compiler rejects the program.
release :: TypedProgram -> Maybe Released
release tp = case verdict tp of
  Safe _ -> Released (tpTmpDim tp) <$> parkedLine tp
  _      -> Nothing

-- The restoration plan

-- | The gate carrying a released temporary from its own ray back to the
-- allocation ray: 'DQT.Criterion.Witness.householder', a reflection that
-- is its own inverse. Exists exactly when the ray is preparable over the
-- coefficient field.
restore :: Int -> Int -> Released -> Either Reason Mat
restore d i0 c = unitOn (releasedRay c) >>= householder d i0

-- | A unit vector on the ray.  Choosing the representative is where the field's
-- square roots are needed; when it has none the plan is unavailable, and that
-- is reported rather than approximated.
unitOn :: Vec -> Either Reason Vec
unitOn g = case ksqrtReal n2 of
  Nothing -> Left (ParkedNormNotInGateRing n2)
  Just n  -> Right (map (`kdiv` n) g)
  where n2 = vnorm2 g

-- | What a restoration costs: one gate, or none.  A clean temporary needs no
-- plan, because the reflection degenerates to the identity; any other
-- temporary needs exactly one, and never a second.
restoreCost :: Int -> Int -> Released -> Maybe Int
restoreCost d i0 c = case restore d i0 c of
  Left _  -> Nothing
  Right r -> Just (if matIsIdentity r then 0 else 1)

-- The weaker rule

-- | The literature's rule: the register rests on the ray it was allocated on.
restoredToAllocation :: TypedProgram -> Bool
restoredToAllocation tp = case parkedLine tp of
  Nothing -> False
  Just g  -> lineEqual g (vbasis (tpTmpDim tp) (tpAlloc tp))

-- | Sound: every program the restoration rule accepts, the criterion accepts.
restorationRuleIsSufficient :: Bool
restorationRuleIsSufficient =
  and [ not (restoredToAllocation tp) || isSafe tp | tp <- typedCatalogue ]

-- | Not complete: the safe programs the restoration rule refuses.  Each
-- entry is a temporary a restore-based compiler would decline to return to
-- the pool although returning it is safe.
restorationRuleIsNotNecessary :: [String]
restorationRuleIsNotNecessary =
  [ n | (n, tp) <- namedCatalogue, isSafe tp, not (restoredToAllocation tp) ]

-- | The gap, as a pair of numbers: how many catalogue
-- programs accept their drop, and how many of those the restoration rule
-- refuses.  It is exported so that both can be pinned by a named check rather
-- than transcribed by hand.
restorationGap :: (Int, Int)
restorationGap =
  ( length [ () | tp <- typedCatalogue, isSafe tp ]
  , length restorationRuleIsNotNecessary )

-- Shared reading of the catalogue

namedCatalogue :: [(String, TypedProgram)]
namedCatalogue = [ (n, tp) | (n, p) <- catalogue, Right tp <- [checkProgram p] ]

typedCatalogue :: [TypedProgram]
typedCatalogue = map snd namedCatalogue

isSafe :: TypedProgram -> Bool
isSafe tp = case verdict tp of
  Safe _ -> True
  _      -> False

-- Reporting

poolReport :: String
poolReport = unlines $
  [ "  what each program releases into the pool, and whether the weaker rule"
  , "  (restored to the allocation ray) would accept it."
  , ""
  , "  " ++ pad 16 "program" ++ pad 30 "certificate released" ++ "restoration rule" ]
  ++ [ "  " ++ pad 16 n ++ pad 30 (certificate tp) ++ rule tp
     | (n, tp) <- namedCatalogue ]
  ++ [ "" ]
  ++ [ "  admissible but refused by the weaker rule:" ]
  ++ [ "    " ++ l | l <- wrapAt 66 (intercalate ", " restorationRuleIsNotNecessary) ]
  ++ [ "  the weaker rule is sound: " ++ show restorationRuleIsSufficient
     , ""
     , "  the restoration rule refuses "
       ++ show (snd restorationGap) ++ " of the " ++ show (fst restorationGap)
       ++ " admissible programs in this catalogue." ]
  where
    pad k s = s ++ replicate (max 0 (k - length s)) ' '
    certificate = maybe "none (drop refused)" show . release
    rule tp = if restoredToAllocation tp then "accepts" else "refuses"
