-- |
-- Module      : DQT.Calculus.Metatheory
--
-- The properties that make the calculus well defined: decidability,
-- progress, preservation, adequacy, and the structural rules, checked
-- over a bounded enumeration.
module DQT.Calculus.Metatheory
  ( -- * The enumeration
    enumeratePrograms
  , enumerationSize
    -- * The properties
  , boundedTypingTotality
  , boundedProgress
  , boundedFinalDimensionCheck
  , machineIsAFunction
  , boundedAdequacy
  , resultTypeIsHonest
  , typingForcesAnIsometry
    -- * The structural rules
  , contractionIsRejected
  , implicitWeakeningIsRejected
  , allocFreeIsEnforced
    -- * Reporting
  , metatheoryReport
  ) where

import DQT.Calculus.Elaborate (agreesWithMachine, coreMap, droppedDims)
import DQT.Calculus.Gates
import DQT.Algebra.Linear
import DQT.Calculus.Machine (Config(..), runTermRaw)
import DQT.Calculus.Syntax
import DQT.Calculus.Typing

-- The enumeration

-- | The canonical-chain family: one allocation of dimension @d@ over a
-- visible register of dimension @m@, a chain of at most @n@ gates, and
-- one of seven fixed tails. Not every program the grammar generates (no
-- nested allocation, no binder collision, no malformed gate): a pass here
-- is a pass on the family, not the grammar. Deliberately includes
-- ill-typed terms (double-drop, never-drop, returns a temporary).
enumeratePrograms :: Int -> Int -> Int -> [Gate] -> [Program]
enumeratePrograms d m n gs =
  [ Program ("enum:" ++ show i) "v" m t | (i, t) <- zip [0 :: Int ..] terms ]
  where
    terms = [ New "t" d 0 body | body <- bodies n "t" "v" (0 :: Int) ]

    -- bodies of length <= k, with the affine renaming the calculus requires
    bodies 0 t v _ = tails t v
    bodies k t v c =
      tails t v
      ++ [ Act (t', v') g (t, v) rest
         | g <- gs
         , gateTmpDim g == d, gateVisDim g == m
         , let t' = "t" ++ show (c + 1)
         , let v' = "v" ++ show (c + 1)
         , rest <- bodies (k - 1) t' v' (c + 1) ]

    -- the ways a body can end: the correct one, and the mistakes
    tails t v =
      [ Drop t (Ret v)          -- well formed
      , Ret v                   -- forgets to drop: implicit weakening
      , Drop t (Ret t)          -- returns a dropped name
      , Drop t (Drop t (Ret v)) -- drops twice
      , Ret t                   -- returns the temporary
      , Pair t v                -- returns a pair, which is not the result type
      , Drop v (Ret v)          -- drops the visible register
      ]

-- | How many programs the default enumeration covers.
enumerationSize :: Int
enumerationSize = length defaultEnumeration

defaultEnumeration :: [Program]
defaultEnumeration =
  enumeratePrograms 2 2 2 [gHt 2, gXt 2, gRead 2, gCopy, gCZ, gIdent 2 2]
  ++ enumeratePrograms 3 3 1 [gTiltT 3, gRead 3, gIdent 3 3]

typed :: [TypedProgram]
typed = [ tp | p <- defaultEnumeration, Right tp <- [checkProgram p] ]

-- The properties

-- | Decidability, operationally: the checker returns an answer on every term
-- of the enumeration.  Here that means forcing the result to a constructor
-- neither diverges nor throws.
boundedTypingTotality :: Bool
boundedTypingTotality = all decided defaultEnumeration
  where decided p = case checkProgram p of
          Left e   -> length (show e) >= 0     -- forces the error message too
          Right tp -> tpTmpDim tp > 0

-- | Progress: every well-typed term runs to a final configuration with no
-- stuck state.  The machine's only partial operation is looking a name up in
-- the register list, so \"no stuck state\" is exactly \"every name the term
-- mentions is live when it is mentioned\", which is what the exact-context
-- discipline buys.
boundedProgress :: Bool
boundedProgress = all runs typed
  where
    runs tp = all (\j -> length (cfgAmp (runTermRaw tp (vbasis (tpVisDim tp) j)))
                          == tpTmpDim tp * tpVisDim tp)
                  [0 .. tpVisDim tp - 1]

-- | Preservation: the dimensions the machine carries are the dimensions
-- the context promises, at the end of every run: one temporary of dimension
-- @d@ and one visible register of dimension @m@, in that tensor order.
boundedFinalDimensionCheck :: Bool
boundedFinalDimensionCheck = all ok typed
  where
    ok tp = all (\j -> cfgDims (runTermRaw tp (vbasis (tpVisDim tp) j))
                        == [tpVisDim tp, tpTmpDim tp])
                [0 .. tpVisDim tp - 1]

-- | The machine is a function.  This is recorded rather than discovered: the
-- machine is a Haskell function, so @f x == f x@ holds by construction and no
-- amount of enumeration makes it informative.  It is kept so that a later
-- change to a nondeterministic machine, a choice of gate order or a monadic
-- transition, has a named line to break instead of passing silently.
machineIsAFunction :: Bool
machineIsAFunction = all ok typed
  where ok tp = let v = vbasis (tpVisDim tp) 0
                in cfgAmp (runTermRaw tp v) == cfgAmp (runTermRaw tp v)

-- | Adequacy: the compositional denotation of "DQT.Calculus.Elaborate" and the
-- operational semantics of "DQT.Calculus.Machine" agree on every well-typed term.
--
-- This is the property with content.  The machine appends the temporary to a
-- register list and applies gates in place; the denotation builds a matrix
-- bottom-up and moves the dropped factor to the front.
boundedAdequacy :: Bool
boundedAdequacy = all agreesWithMachine typed

-- | The result type is honest about the register count: exactly the
-- temporaries the term drops are dropped, and the denotation has the shape the
-- type says.
resultTypeIsHonest :: Bool
resultTypeIsHonest =
  all (\tp -> droppedDims tp == [tpTmpDim tp]
              && length (coreMap tp) == tpTmpDim tp * tpVisDim tp)
      typed

-- | Typing forces an isometry, @K^dagger K = 1@: the one fact the type system
-- contributes to the criterion, checked over the enumeration rather than over
-- the catalogue.
typingForcesAnIsometry :: Bool
typingForcesAnIsometry =
  all (\tp -> matMul (matConjTranspose (coreMap tp)) (coreMap tp)
              == matId (tpVisDim tp))
      typed

-- The structural rules

-- | Contraction is rejected: @\<v, v\>@ does not type, because the @Pair@ rule
-- requires distinct names.  The deeper reason is not a rule at all: the map
-- that would implement contraction, @u |-> u (x) u@, is not linear, so there
-- would be nothing for such a rule to denote.
contractionIsRejected :: Bool
contractionIsRejected =
  case checkProgram (Program "contraction" "v" 2 (New "t" 2 0 (Pair "v" "v"))) of
    Left _  -> True
    Right _ -> False

-- | Implicit weakening is rejected: a term that lets the temporary fall
-- out of scope without a @drop@ does not type; the error names the leftover.
-- This is the whole reason the calculus has an exact-context discipline.
implicitWeakeningIsRejected :: Bool
implicitWeakeningIsRejected =
  case checkProgram (Program "implicit weakening" "v" 2 (New "t" 2 0 (Ret "v"))) of
    Left (LeftoverNames _) -> True
    _                      -> False

-- | The single-scope premise is enforced: a second allocation inside an
-- allocation body is rejected, with the error that names the premise.
allocFreeIsEnforced :: Bool
allocFreeIsEnforced =
  case checkProgram (Program "nested" "v" 2
                       (New "t" 2 0 (New "s" 2 0 (Drop "s" (Drop "t" (Ret "v")))))) of
    Left AllocInBody -> True
    _                -> False

-- Reporting

metatheoryReport :: String
metatheoryReport = unlines
  [ "  the calculus, checked over " ++ show enumerationSize
    ++ " enumerated programs (" ++ show (length typed) ++ " of them well typed)"
  , ""
  , "  Argued by inspection, one case per constructor in DQT.Calculus.Typing.typeOf:"
  , "    rule selection      the outer constructor fixes the only possible final"
  , "                        rule, for a fixed context and term"
  , "    mode-correctness    context and term are inputs and the type is the"
  , "                        output; no premise input is guessed"
  , "    termination         every recursive call is on the body subterm, and"
  , "                        every side condition decides"
  , "    functionality       hence at most one type for a fixed context and term."
  , "                        Not one derivation per term, which is false:"
  , "                        v:tmp[2] |- v and v:vis[3] |- v are both derivable"
  , "    exchange            invisible: contexts are finite partial maps"
  , ""
  , "  Not checked here:"
  , "    typeOf g e == Right a  <->  g |- e : a"
  , "    (soundness and completeness of the checker against the printed rules;"
  , "     a total deterministic function is not automatically an implementation)"
  , ""
  , "  Checked over the canonical-chain enumeration:"
  , "    typing is total          " ++ show boundedTypingTotality
  , "    progress                 " ++ show boundedProgress
  , "    final dimensions         " ++ show boundedFinalDimensionCheck
  , "    adequacy (machine = den) " ++ show boundedAdequacy
  , "    result type is honest    " ++ show resultTypeIsHonest
  , "    typing forces isometry   " ++ show typingForcesAnIsometry
  , ""
  , "  True by construction, recorded so a future change fails a named line:"
  , "    machine is a function    " ++ show machineIsAFunction
  , "    (the machine is a Haskell function, so this cannot fail while the"
  , "     transition stays total; it is not evidence of anything)"
  , ""
  , "  Structural rules, each with its witness:"
  , "    contraction rejected     " ++ show contractionIsRejected
  , "    implicit weakening rej.  " ++ show implicitWeakeningIsRejected
  , "    allocFree enforced       " ++ show allocFreeIsEnforced
  , ""
  , "  A bound is not a proof, and it is narrower than every program."
  , "  The generator emits one allocation, a chain of gates drawn from a fixed"
  , "  repertoire with canonical binder names, and one of seven fixed tails."
  , "  It never emits a nested allocation, a binder collision, or a malformed"
  , "  gate. What it buys is that no counterexample exists in that family."
  ]
