-- Teleport.hs: teleportation, one of the suite's algorithms.
--
-- The criterion accepts both drops at every selection: after the Bell
-- measurement each temporary sits on a fixed line per selection, so a
-- measurement alone does not make a drop hard. The runtime check must
-- decline instead, since the prefix entangles m and a with b.

module S.Programs.Teleport where

import S.Lang.Ring
import S.Lang.QState
import S.Lang.Gates
import S.Lang.Syntax
import S.Lang.Interp
import S.Pass

visT :: VisSpec
visT = [("b", 2)]

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
  , IfBit "w" [] [Gate gX ["b"]]
  , IfBit "z" [] [Gate gZ ["b"]]
  , Drop "m"
  , Drop "a"
  ]

teleportProg :: Matrix QS2 -> Prog QS2
teleportProg = teleportF

teleP :: Prog QS2
teleP = teleportProg gH                -- the message |+>

sels4 :: [[Sel]]
sels4 = allSelections 2

-- | The factor on b of the final state: what was teleported.
bFactor :: [Sel] -> Maybe (StateV QS2)
bFactor sel =
  let m = runStmts (initMach visT (ket [2] [0])) teleP sel Nothing
  in fst <$> factorSplit (mDims m) [regPos m "b"] (mAmp m)

checks :: [(String, Bool)]
checks = concat
  [ [ ("teleport drop " ++ tgt ++ " admissible at selection "
       ++ show (map selBit sel)
      , semanticVerdict visT teleP tgt sel == Admissible)
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
