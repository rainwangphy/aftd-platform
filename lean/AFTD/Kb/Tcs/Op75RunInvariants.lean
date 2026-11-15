import AFTD.Prelude
import AFTD.Kb.Tcs.Op75Run
import AFTD.Kb.Tcs.Op75CompactMap
import AFTD.Kb.Tcs.Op75CompactDigit

/-!
# op75_run_invariants

Topic: np_completeness   Node: e4aaebd4fabf

Provenance: helper lemma. OP-75, arXiv:2610.06092: proof of the explicit single-pass subset-sum network.

For nonnegative integer weights and a starting point in the unit interval, the compact orbit remains in the unit interval and its accumulated digit-weighted sum is nonnegative.
-/

lemma op75_run_invariants (as : List ℕ) (x : ℝ) (hx : x ∈ Set.Icc 0 1) :
    (op75_run op75_compact_map op75_compact_digit (as.map fun a : ℕ => (a:ℝ)) x).1 ∈ Set.Icc 0 1 ∧
    0 ≤ (op75_run op75_compact_map op75_compact_digit (as.map fun a : ℕ => (a:ℝ)) x).2 := by
  induction as generalizing x with
  | nil => simpa [op75_run] using hx
  | cons a as ih =>
      have hF : op75_compact_map x ∈ Set.Icc (0:ℝ) 1 := by
        constructor
        · unfold op75_compact_map
          exact le_min (by norm_num) (le_min (by linarith [hx.1]) (abs_nonneg _))
        · exact min_le_left _ _
      have hE : 0 ≤ op75_compact_digit x := le_max_left _ _
      have h := ih (op75_compact_map x) hF
      simp only [List.map_cons, op75_run]
      exact ⟨h.1, add_nonneg (mul_nonneg (Nat.cast_nonneg a) hE) h.2⟩
