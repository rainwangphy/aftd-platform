import AFTD.Prelude
import AFTD.Kb.Tcs.UnitHammingMaxTriangleFree
import AFTD.Kb.Tcs.UnitHammingTriangleFreeCardLe
import AFTD.Kb.Tcs.ExistsUnitHammingTriangleFreeCardEq
import AFTD.Kb.Tcs.UnitHammingTriangleFree

/-!
# unit_hamming_max_triangle_free_eq

Topic: combinatorics   Node: 4e28baa09fea

Provenance: formalization of a published result. Source: arXiv:2610.32789 Theorem 1.3

For every fixed integer q ≥ 2 and every integer n ≥ 1, the maximum size unit_hamming_max_triangle_free n q of a triangle-free vertex subset of (Fin n → Fin q) in the unit-distance Hamming graph equals 2 * q ^ (n - 1).
-/

/-- Maximum size of a triangle-free set in the unit-distance Hamming graph: T_q(n, 1) = 2 * q^(n-1). -/
theorem unit_hamming_max_triangle_free_eq (n q : ℕ) (hq : 2 ≤ q) (hn : 1 ≤ n) :
    unit_hamming_max_triangle_free n q = 2 * q ^ (n - 1) := by
  unfold unit_hamming_max_triangle_free
  apply csSup_eq_of_forall_le_of_forall_lt_exists_gt
  · obtain ⟨A, hA, hcard⟩ := exists_unit_hamming_triangle_free_card_eq n q hq hn
    exact ⟨2 * q ^ (n - 1), A, hA, hcard⟩
  · rintro a ⟨A, hA, rfl⟩
    exact unit_hamming_triangle_free_card_le n q hq hn A hA
  · intro w hw
    obtain ⟨A, hA, hcard⟩ := exists_unit_hamming_triangle_free_card_eq n q hq hn
    exact ⟨2 * q ^ (n - 1), ⟨A, hA, hcard⟩, hw⟩
