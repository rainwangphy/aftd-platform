import AFTD.Prelude
import AFTD.Kb.Tcs.CssQuasiTransversalCczCode
import AFTD.Kb.Tcs.CssZDistanceGeThreeIffCols
import AFTD.Kb.Tcs.CampbellHowardConditions
import AFTD.Kb.Tcs.CssZDistanceGeThree

/-!
# op_159_css_ccz_no_code_s_zero

Topic: quantum   Node: 75ddbdc27d22

Provenance: helper lemma. arXiv:2610.09341 Sec. 4.2

For any block length n, no 3 by n logical X-operator matrix K and 0 by n X-stabilizer matrix S over ZMod 2 form a CSS quasi-transversal CCZ code.
-/

/-- No CSS code with 3 logical qubits and quasi-transversal CCZ exists at stabilizer rank s = 0. -/
theorem op_159_css_ccz_no_code_s_zero (n : ℕ)
    (K : Matrix (Fin 3) (Fin n) (ZMod 2)) (S : Matrix (Fin 0) (Fin n) (ZMod 2)) :
    ¬ css_quasi_transversal_ccz_code n 0 K S := by
  intro h
  rw [css_quasi_transversal_ccz_code] at h
  obtain ⟨hz, hch⟩ := h
  rw [css_z_distance_ge_three_iff_cols] at hz
  obtain ⟨hz1, hz2⟩ := hz
  have hS : ∀ j : Fin n, S.transpose j = 0 := fun j => by
    funext i; exact i.elim0
  have hK : ∀ (i : Fin 3) (j : Fin n), K i j = 0 := fun i j => by
    have h' := congrFun (hz1 j (hS j)) i
    simpa using h'
  obtain ⟨_, _, h3, _⟩ := hch
  have hsum : (∑ j, K 0 j * K 1 j * K 2 j) = 0 := by
    apply Finset.sum_eq_zero
    intro j _
    rw [hK 0 j, hK 1 j, hK 2 j]
    ring
  rw [hsum] at h3
  exact zero_ne_one h3
