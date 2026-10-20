import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PickingPhiEntry
import AFTD.Kb.GameTheoryEconomics.RoundRobinSequence

/-!
# round_robin_phi_vector

Topic: fair_division   Node: b7c4f91b9078

Provenance: helper lemma. step towards round_robin_item_preserving_swaps_polynomial_convergence

The potential of arXiv:2610.23040 (Thm 3.13) for Round Robin with n agents and m goods: the vector Phi(r) = (phi_0(r), ..., phi_{m-1}(r)) of the 0-based ranks of the items selected at each of the m turns.
-/

/-- The lexicographic potential Phi for the Round-Robin sequence. -/
def round_robin_phi_vector {n : ℕ} [NeZero n] (m : ℕ) (rank : Fin n → Fin m ≃ Fin m) : List ℕ := List.ofFn (fun s : Fin m => picking_phi_entry (round_robin_sequence n m) rank s.val)
