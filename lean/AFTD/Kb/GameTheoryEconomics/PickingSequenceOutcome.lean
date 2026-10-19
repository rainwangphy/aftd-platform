import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PickingTurn

/-!
# picking_sequence_outcome

Topic: fair_division   Node: fd3a05aa4a8d

Provenance: formalization of a published result. Source: arXiv:2610.23040 (On the Convergence of Iterated Round Robin), Sec. 2; also arXiv:2610.23686 Sec. 2

The allocation returned by the picking-sequence mechanism PS_π: agents act in the order seq, and at each turn the active agent takes its highest-ranked remaining good, where rank i k is the good agent i reports in position k (position 0 is its top good).
-/

/-- The allocation of the picking-sequence mechanism `PS_π`: agents act in the order `seq`, and at each turn the active agent takes its highest-ranked available good; `rank i k` is the good agent `i` reports in position `k` (position `0` best). -/
def picking_sequence_outcome {N G : Type*} [DecidableEq N] [DecidableEq G]
    {m : ℕ} (seq : List N) (rank : N → Fin m ≃ G) : N → Finset G :=
  (seq.foldl (fun st i => picking_turn (List.ofFn (rank i)) i st) (fun _ => ∅, ∅)).1
