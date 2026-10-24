import AFTD.Prelude

/-!
# hasDerivAt_comp_affine_at_zero

Topic: information   Node: 4e866aa4f7c5

Provenance: helper lemma. arXiv:2610.21231 (On the subadditivity of mutual f-information), Appendix B, proof of Lemma 4

If g has derivative g' at c, then t ↦ g(c + t d) has derivative g' d at 0.
-/

theorem hasDerivAt_comp_affine_at_zero (gw : ℝ → ℝ) (gw' c d : ℝ) (h : HasDerivAt gw gw' c) :
    HasDerivAt (fun t : ℝ => gw (c + t * d)) (gw' * d) 0 := by
  have hh : HasDerivAt (fun t : ℝ => c + t * d) d 0 := by
    simpa using ((hasDerivAt_id' (0:ℝ)).mul_const d).const_add c
  have h' : HasDerivAt gw gw' ((fun t : ℝ => c + t * d) 0) := by simpa using h
  exact h'.comp (h := fun t : ℝ => c + t * d) 0 hh
