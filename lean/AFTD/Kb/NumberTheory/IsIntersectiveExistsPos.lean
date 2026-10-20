import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.NumberTheory.IsIntersective
import AFTD.Kb.Tcs.CslibSKIPolynomialEval

/-!
# is_intersective_exists_pos

Topic: elementary_number_theory   Node: f6cead1fd80b

Provenance: helper lemma. step towards op_153_subexp_bound_intersective_quadratic

If h ∈ ℤ[X] is intersective and m is a positive integer, there exists a positive integer n > 0 such that h(n) ≡ 0 (mod m).
-/

lemma is_intersective_exists_pos_eval_modEq (p : Polynomial ℤ) (a b : ℤ) (m : ℤ) (h : a ≡ b [ZMOD m]) :
    p.eval a ≡ p.eval b [ZMOD m] := by
  rw [Int.modEq_iff_dvd] at *
  exact dvd_trans h (p.sub_dvd_eval_sub b a)

/-- An intersective polynomial has a positive integer root modulo every positive integer m. -/
theorem is_intersective_exists_pos (h : Polynomial ℤ) (hh : is_intersective h) (m : ℕ) (hm : 0 < m) :
    ∃ n : ℕ, 0 < n ∧ h.eval (n : ℤ) ≡ 0 [ZMOD m] := by
  rcases hh m hm with ⟨r, hr⟩
  have hm_pos : 0 < (m : ℤ) := Int.natCast_pos.mpr hm
  have h_emod_nonneg := Int.emod_nonneg r (ne_of_gt hm_pos)
  have h_pos : 0 < r % (m : ℤ) + (m : ℤ) := by linarith
  have h_nonneg : 0 ≤ r % (m : ℤ) + (m : ℤ) := by linarith
  set n := (r % (m : ℤ) + (m : ℤ)).toNat with hn_def
  refine ⟨n, ?_, ?_⟩
  · rw [hn_def, ← Int.natCast_pos, Int.toNat_of_nonneg h_nonneg]
    exact h_pos
  · have hnr : (n : ℤ) ≡ r [ZMOD m] := by
      rw [Int.ModEq, hn_def, Int.toNat_of_nonneg h_nonneg]
      simp
    exact (is_intersective_exists_pos_eval_modEq h (n : ℤ) r m hnr).trans hr
