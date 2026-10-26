-- Drop.Lang.Compile.Reuse: which wires a later allocation may take over.
--
-- Question: Which wires may a later allocation take over?
-- Answer:   compile gives every allocation fresh qubits; compileReuse lets a later allocation take
--           over the qubits a drop returned. reuseLayout
--           walks the program in order with a pool of freed qubits. A block enters the pool at its
--           drop when every register it names was allocated on a basis state and the drop has a
--           temporary certificate (SafeCert) on every reachable record; the drop then also clears
--           the qubits whose allocation bit is 1 (liPoolClears). A later allocation on a basis
--           state takes qubits from the pool first and fresh ones for the rest; any other
--           allocation is given fresh qubits. Inputs and loans keep their wires, and a loan,
--           being a register without an allocation vector, never enters the pool. There is one
--           wire map for all records.
-- Paper:    sec:eval:compile (compile-reuse), app:emitter-contract.
-- Shapes:   LayoutInfo  the layout of Drop.Lang.Compile.Layout; reuseLayout returns it with
--                       liWireQ, liLiftAncilla, liTotalQubits and liPoolClears replaced.

module Drop.Lang.Compile.Reuse
  ( reuseLayout
  ) where

import qualified Data.Map.Strict as Map

import Drop.Lang.Compile.Layout
import Drop.Lang.Compile.Safety
import Drop.Lang.Scalar (Cyclo)
import Drop.Lang.Syntax

-- | The layout with wires reused. Reuse has one wire map for all records. A
-- block enters the pool only when every reachable record has a temporary
-- certificate and every allocation in the block is a basis state. Loans and
-- inputs stay separate. The result is the original layout with its wire map,
-- lift ancillas, qubit total and pool clears replaced.
reuseLayout :: Program Cyclo -> SafetyInfo -> LayoutInfo -> LayoutInfo
reuseLayout prog safety original = finish (walk start (toTerm (progTerm prog)))
  where
    inputQs = concatMap (wireQubits original . fst) (progCtx prog)
    start = (original { liWireQ = Map.restrictKeys (liWireQ original)
                        (Map.keysSet (Map.fromList (progCtx prog)))
                      , liLiftAncilla = Map.empty }, length inputQs, [])
    allocations = Map.fromList
      [ (n, psi) | StNew n _ psi <- statements (toTerm (progTerm prog)) ]
    finish (l, next, _) = l { liTotalQubits = next }
    reserve k next = ([next .. next + k - 1], next + k)
    walk st (Return _) = st
    walk st (If _ a _) = walk st a
    walk (l, next, pool) (Do stmt rest) = walk st' rest
      where
        st' = case stmt of
          StNew n d psi ->
            let k = ilog2 d
                used = case basisIndexOfExact psi of
                         Just _ -> take k pool
                         Nothing -> []
                (extra, next') = reserve (k - length used) next
                l' = l { liWireQ = Map.insert n (used ++ extra) (liWireQ l) }
            in (l', next', drop (length used) pool)
          StLoan n d ->
            let (qs, next') = reserve (ilog2 d) next
            in (l { liWireQ = Map.insert n qs (liWireQ l) }, next', pool)
          StLift n _ _ | Map.member n (liLiftAncilla original) ->
            (l { liLiftAncilla = Map.insert n next (liLiftAncilla l) }, next + 1, pool)
          StDrop site v | let names = valueNames v
                       , not (null names)
                       , Just bases <- traverse (\n -> Map.lookup n allocations >>= basisIndexOfExact) names
                       , let live = filter (/= UnreachableOutcome)
                                      (Map.elems (Map.findWithDefault Map.empty site safety))
                       , not (null live), all temporaryCert live ->
            let qs = concatMap (wireQubits l) names
                clears = concat [ [ q | (q, b) <- zip (wireQubits l n)
                                                    (bitsOfIndex (length (wireQubits l n)) i), b == 1 ]
                                | (n, i) <- zip names bases ]
            in (l { liPoolClears = Map.insert site clears (liPoolClears l) }, next, pool ++ qs)
          _ -> (l, next, pool)
    temporaryCert (SafeCert _) = True
    temporaryCert _ = False

-- Two disjoint lifetimes (two-phases.s): the second temporary takes over the wire of the first, so one qubit is saved.
-- >>> :m + Drop.Lang.Parser
-- >>> readFile "programs/two-phases.s" >>= \src -> either putStrLn (\prog -> print (do { l <- layoutProgram prog; sf <- fragmentSafety prog (toTerm (progTerm prog)) l; Right (liWireQ l, liWireQ (reuseLayout prog sf l)) })) (parseTyped src)
-- Right (fromList [("t",[1]),("u",[2]),("x",[0])],fromList [("t",[1]),("u",[1]),("x",[0])])
-- >>> readFile "programs/two-phases.s" >>= \src -> either putStrLn (\prog -> print (do { l <- layoutProgram prog; sf <- fragmentSafety prog (toTerm (progTerm prog)) l; Right (liTotalQubits l, liTotalQubits (reuseLayout prog sf l)) })) (parseTyped src)
-- Right (3,2)

-- The first block was allocated on |0>, so its drop clears nothing; the second was allocated on |1>, so its drop clears its wire.
-- >>> readFile "programs/two-phases.s" >>= \src -> either putStrLn (\prog -> print (do { l <- layoutProgram prog; sf <- fragmentSafety prog (toTerm (progTerm prog)) l; Right (liPoolClears (reuseLayout prog sf l)) })) (parseTyped src)
-- Right (fromList [(0,[]),(1,[1])])

-- Nothing is allocated after the drop in temp-and.s: the layout does not change.
-- >>> readFile "programs/temp-and.s" >>= \src -> either putStrLn (\prog -> print (do { l <- layoutProgram prog; sf <- fragmentSafety prog (toTerm (progTerm prog)) l; Right (liTotalQubits l, liTotalQubits (reuseLayout prog sf l)) })) (parseTyped src)
-- Right (3,3)

-- A loan is never pooled: mcx-dirty-x.s keeps all five wires.
-- >>> readFile "programs/mcx-dirty-x.s" >>= \src -> either putStrLn (\prog -> print (do { l <- layoutProgram prog; sf <- fragmentSafety prog (toTerm (progTerm prog)) l; Right (liTotalQubits (reuseLayout prog sf l), liPoolClears (reuseLayout prog sf l)) })) (parseTyped src)
-- Right (5,fromList [])

-- An unsafe drop is not pooled: copy-input.s allocates t and drops the input x, which is left unsafe.
-- >>> readFile "programs/copy-input.s" >>= \src -> either putStrLn (\prog -> print (do { l <- layoutProgram prog; sf <- fragmentSafety prog (toTerm (progTerm prog)) l; Right (liTotalQubits l, liTotalQubits (reuseLayout prog sf l)) })) (parseTyped src)
-- Right (2,2)
