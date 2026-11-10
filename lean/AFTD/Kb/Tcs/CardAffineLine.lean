import AFTD.Prelude
import AFTD.Kb.Tcs.AffineLine

/-!
# card_affine_line

Topic: combinatorics   Node: 1a99158d2c1c

Provenance: helper lemma. arXiv:2611.12153 Section 2

Let p be a prime. For any point P and nonzero direction vector v in (ZMod p)^3, the affine line through P in direction v has cardinality p.
-/

/-- An affine line in (ZMod p)^3 with nonzero direction vector has cardinality p. -/
theorem card_affine_line (p : ℕ) [Fact p.Prime] (P v : Fin 3 → ZMod p) (hv : v ≠ 0) :
    (affine_line P v).ncard = p := by
  have hinj : Function.Injective (fun t : ZMod p => P + t • v) := by
    intro a b hab
    simp only [add_right_inj] at hab
    have h : (a - b) • v = 0 := by rw [sub_smul, hab, sub_self]
    have hz : a - b = 0 := by
      rcases smul_eq_zero.mp h with h' | h'
      · exact h'
      · exact absurd h' hv
    exact sub_eq_zero.mp hz
  have hset : affine_line P v = Set.range (fun t : ZMod p => P + t • v) := by
    ext x
    simp [affine_line, Set.mem_range, eq_comm]
  rw [hset, Set.ncard_range_of_injective hinj, Nat.card_eq_fintype_card]
  exact ZMod.card p
