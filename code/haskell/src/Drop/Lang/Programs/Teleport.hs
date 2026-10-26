-- Drop.Lang.Programs.Teleport: teleportation, and its two temporaries.
--
-- Question: Are the two temporaries of teleportation safe to drop after the Bell measurement?
-- Answer:   The message qubit m (prepared by a gate P) and Alice's half a of a Bell pair are the
--           temporaries; Bob's qubit b is visible, supplied in |0>. After the Bell measurement,
--           two lifts, each temporary sits on a fixed line for each selection, so the criterion
--           accepts both drops at every one of the four selections: a measurement alone does not
--           make a drop hard. The corrections fire on bit 0 (the lift's bit is 1 when the
--           measured block {0} survives), and at every selection b carries the message, here |+>.
--           The static pass of Drop.Lang.Pass must decline at both drops, depth 2 and four rows,
--           since the prefix entangles m and a with b (prefix-parks).
-- Paper:    sec:meas:programs (the program, as teleport.s), fig:teleport-records (it as a circuit),
--           sec:residual (the reclaiming gate per record), app:corpus.
-- Shapes:   visT             the visible register: b, two levels.
--           teleportF p      the program for the message gate p: m prepared, the Bell pair, the
--                            Bell measurement as two lifts, the corrections, drop m, drop a.
--           teleP            teleportF with p = H, the message |+>.
--           sels4            the four selections of the two lifts.
-- Corpus file: programs/teleport.s holds teleP; the check "programs/teleport.s is the module's
--           program as syntax" pairs them, and "teleport.s verdicts agree with ExTeleport at both
--           drops" compares verdicts.

module Drop.Lang.Programs.Teleport where

import Drop.Lang.Scalar
import Drop.Lang.State
import Drop.Lang.Gates
import Drop.Lang.Flat
import Drop.Lang.Interp
import Drop.Lang.Criterion
import Drop.Lang.Pass

visT :: VisSpec
visT = [("b", 2)]

-- >>> visT
-- [("b",2)]

-- | P prepares the message on m.
teleportF :: Matrix QS2 -> Prog QS2
teleportF p =
  [ New "m" 2
  , Gate p ["m"]
  , New "a" 2
  , Gate gH ["a"]
  , Gate gCX ["a", "b"]
  , Gate gCX ["m", "a"]
  , Gate gH ["m"]
  -- Lift convention: the bit is 1 when the measured block {0} survives,
  -- that is, when the outcome is 0.  The corrections therefore fire on bit
  -- 0; getting that backwards still gives every drop the same verdict,
  -- since a fixed unitary on b never changes the factorisation, but no
  -- longer teleports.  The check on b's factor below is the one that
  -- notices.
  , Lift "z" "m" [0]
  , Lift "w" "a" [0]
  , IfBit (GParam "w") [] [Gate gX ["b"]]
  , IfBit (GParam "z") [] [Gate gZ ["b"]]
  , Drop ["m"]
  , Drop ["a"]
  ]

-- Thirteen commands, whatever the message gate.
-- >>> length (teleportF gH)
-- 13

teleportProg :: Matrix QS2 -> Prog QS2
teleportProg = teleportF

teleP :: Prog QS2
teleP = teleportProg gH                -- the message |+>

-- The program as text.
-- >>> :m + Drop.Lang.Render Drop.Lang.Parser
-- >>> mapM_ (putStrLn . renderCmd) (mapProg embedQS2 teleP)
-- new m : [2] @ |0>;
-- H m;
-- new a : [2] @ |0>;
-- H a;
-- CX a b;
-- CX m a;
-- H m;
-- z = lift[{0}] m;
-- w = lift[{0}] a;
-- if w { } else { X b; }
-- if z { } else { Z b; }
-- drop m;
-- drop a;

-- It is the text of programs/teleport.s, parsed.
-- >>> readFile "programs/teleport.s" >>= \src -> print (fmap (== (visT, mapProg embedQS2 teleP)) (parseProgram src))
-- Right True

-- Both drops are safe at all four selections.
-- >>> [ (drSite r, map snd (drRows r)) | r <- verdict visT teleP ]
-- [(["m"],[Safe,Safe,Safe,Safe]),(["a"],[Safe,Safe,Safe,Safe])]

-- The static pass declines at both: two lifts before the drop, four rows, and the prefix does not park.
-- >>> [ (x, rDepth r, length (rTable r), lookup "prefix-parks" (rHyps r)) | x <- ["m", "a"], let r = residualCheck visT teleP x ]
-- [("m",2,4,Just False),("a",2,4,Just False)]

-- >>> map reVerdict (rTable (residualCheck visT teleP "m"))
-- [HypothesesFail,HypothesesFail,HypothesesFail,HypothesesFail]

sels4 :: [[Sel]]
sels4 = allSelections 2

-- >>> sels4
-- [[SIn,SIn],[SIn,SOut],[SOut,SIn],[SOut,SOut]]

-- | The factor on b of the final state: what was teleported.
bFactor :: [Sel] -> Maybe (StateV QS2)
bFactor sel =
  let m = runStmts (initMach visT (ket [2] [0])) teleP sel Nothing
  in fst <$> factorSplit (mDims m) [regPos m "b"] (mAmp m)

-- At every selection b carries the message |+>, up to a scalar.
-- >>> [ fmap (\v -> stateProportional v [1, 1]) (bFactor sel) | sel <- sels4 ]
-- [Just True,Just True,Just True,Just True]

-- The suite's claims ------------------------------------------------------------------

checks :: [(String, Bool)]
checks = concat
  [ [ ("teleport drop " ++ tgt ++ " safe at selection "
       ++ show (map selBit sel)
      , semanticVerdict visT teleP tgt sel == Safe)
    | tgt <- ["m", "a"], sel <- sels4 ]
  , [ ("teleport drop " ++ tgt
       ++ ": runtime check depth 2, table 4, declines, parking fails"
      , let r = residualCheck visT teleP tgt
        in rDepth r == 2 && length (rTable r) == 4
           && all ((== HypothesesFail) . reVerdict) (rTable r)
           && lookup "prefix-parks" (rHyps r) == Just False)
    | tgt <- ["m", "a"] ]
  , [ ("teleport: b carries the message at selection " ++ show (map selBit sel)
      , case bFactor sel of
          Just vb -> stateProportional vb [1, 1]
          Nothing -> False)
    | sel <- sels4 ]
  ]

-- >>> length checks
-- 14

-- >>> map fst (take 1 checks)
-- ["teleport drop m safe at selection [1,1]"]
