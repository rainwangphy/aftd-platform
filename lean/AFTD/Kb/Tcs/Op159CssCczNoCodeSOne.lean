import AFTD.Prelude
import AFTD.Kb.Tcs.CssQuasiTransversalCczCode
import AFTD.Kb.Tcs.CssZDistanceGeThreeIffCols
import AFTD.Kb.Tcs.CssZDistanceGeThree
import AFTD.Kb.Tcs.CampbellHowardConditions

/-!
# op_159_css_ccz_no_code_s_one

Topic: quantum   Node: bf9e2c57eccb

Provenance: helper lemma. arXiv:2610.09341 Sec. 4.2

For any block length n, no 3 by n logical X-operator matrix K and 1 by n X-stabilizer matrix S over ZMod 2 form a CSS quasi-transversal CCZ code.
-/

/-- No CSS code with 3 logical qubits and quasi-transversal CCZ exists at stabilizer rank s = 1. -/
theorem op_159_css_ccz_no_code_s_one (n : ℕ)
    (K : Matrix (Fin 3) (Fin n) (ZMod 2)) (S : Matrix (Fin 1) (Fin n) (ZMod 2)) :
    ¬ css_quasi_transversal_ccz_code n 1 K S := by
  have fin1_eq_zero : ∀ (f : Fin 1 → ZMod 2), f 0 = 0 → f = 0 := by
    intro f h
    ext ⟨i, hi⟩
    have : i = 0 := by omega
    subst this
    exact h
  have fin1_eq : ∀ (f g : Fin 1 → ZMod 2), f 0 = g 0 → f = g := by
    intro f g h
    ext ⟨i, hi⟩
    have : i = 0 := by omega
    subst this
    exact h
  intro ⟨hdist, hCH⟩
  rcases (css_z_distance_ge_three_iff_cols K S).mp hdist with ⟨hzero, heq⟩
  rcases hCH with ⟨_, _, hK3, _, _, _, hS1, _, _⟩
  have hS1_0 : ∑ j : Fin n, S 0 j = 0 := hS1 0
  have hz_cube : ∀ x : ZMod 2, x * x * x = x := by decide
  have hz_cases : ∀ x : ZMod 2, x = 0 ∨ x = 1 := by decide
  by_cases hex : ∃ j0 : Fin n, S 0 j0 = 1
  · rcases hex with ⟨j0, hj0⟩
    set v := K.transpose j0
    have hK : ∀ (i : Fin 3) (j : Fin n), K i j = v i * S 0 j := by
      intro i j
      rcases hz_cases (S 0 j) with hs0 | hs1
      · have : S.transpose j = 0 := fin1_eq_zero (S.transpose j) hs0
        have : K.transpose j = 0 := hzero j this
        have : K i j = 0 := congr_fun this i
        rw [this, hs0, mul_zero]
      · have hSeq : S.transpose j = S.transpose j0 :=
          fin1_eq (S.transpose j) (S.transpose j0)
            (by rw [Matrix.transpose_apply, Matrix.transpose_apply, hs1, hj0])
        have hKeq : K.transpose j = v := by
          by_cases hjj : j = j0
          · rw [hjj]
          · exact heq j j0 hjj hSeq
        have : K i j = v i := congr_fun hKeq i
        rw [this, hs1, mul_one]
    have hterm : ∀ j : Fin n, K 0 j * K 1 j * K 2 j = (v 0 * v 1 * v 2) * S 0 j := by
      intro j
      rw [hK 0 j, hK 1 j, hK 2 j]
      have : (v 0 * S 0 j) * (v 1 * S 0 j) * (v 2 * S 0 j) = (v 0 * v 1 * v 2) * (S 0 j * S 0 j * S 0 j) := by ring
      rw [this, hz_cube]
    have hsum : (∑ j : Fin n, K 0 j * K 1 j * K 2 j) = (v 0 * v 1 * v 2) * ∑ j : Fin n, S 0 j := by
      simp_rw [hterm]
      rw [← Finset.mul_sum]
    rw [hS1_0, mul_zero] at hsum
    rw [hsum] at hK3
    revert hK3; decide
  · have hKzero : ∀ j : Fin n, K 0 j = 0 := by
      intro j
      have hs : S 0 j = 0 := by
        rcases hz_cases (S 0 j) with h0 | h1
        · exact h0
        · exact False.elim (hex ⟨j, h1⟩)
      have : S.transpose j = 0 := fin1_eq_zero (S.transpose j) hs
      have : K.transpose j = 0 := hzero j this
      exact congr_fun this 0
    have hsum : (∑ j : Fin n, K 0 j * K 1 j * K 2 j) = 0 := by
      have : (fun j : Fin n => K 0 j * K 1 j * K 2 j) = (fun _ => 0) := by
        ext j
        rw [hKzero j, zero_mul, zero_mul]
      rw [this, Finset.sum_const_zero]
    rw [hsum] at hK3
    revert hK3; decide
