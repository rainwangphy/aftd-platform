import AFTD.Prelude
import AFTD.Kb.Tcs.KstCodeMaxDensityAntitone
import AFTD.Kb.Tcs.K22CodeMaxDensityTwoPowGe
import AFTD.Kb.Tcs.KstCodeMaxDensity

/-!
# k22_code_max_density_ge_inv_pow_two

Topic: combinatorics   Node: 05e659c92c8f

Provenance: helper lemma. step towards four_cycle_graph_code_asymptotic_density_eventually_ge

For any natural numbers n and r such that n ≤ 2^r and 2 ≤ r, the maximum density of a K_{2,2}-code on Fin n is at least 1 / 2^r.
-/

private lemma k22_code_max_density_ge_inv_pow_two_antitone_le (s t : ℕ) (hs : 1 ≤ s) (ht : 1 ≤ t)
    {n m : ℕ} (h : n ≤ m) : kst_code_max_density s t m ≤ kst_code_max_density s t n := by
  induction h with
  | refl => exact le_rfl
  | step h ih => exact le_trans (kst_code_max_density_antitone s t _ hs ht) ih

/-- For any natural numbers n and r such that n ≤ 2^r and 2 ≤ r, the maximum density of a K_{2,2}-code on Fin n is at least 1 / 2^r. -/
theorem k22_code_max_density_ge_inv_pow_two (n r : ℕ) (hn : n ≤ 2 ^ r) (hr : 2 ≤ r) :
    1 / ((2 : ℝ) ^ r) ≤ kst_code_max_density 2 2 n := by
  have hmono : kst_code_max_density 2 2 (2 ^ r) ≤ kst_code_max_density 2 2 n :=
    k22_code_max_density_ge_inv_pow_two_antitone_le 2 2 (by norm_num) (by norm_num) hn
  exact le_trans (k22_code_max_density_two_pow_ge r hr) hmono
