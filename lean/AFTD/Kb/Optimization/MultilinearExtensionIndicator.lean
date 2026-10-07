import AFTD.Prelude
import AFTD.Kb.Optimization.MultilinearExtension
import AFTD.Kb.Optimization.FinsetIndicatorVec

/-!
# multilinear_extension_indicator

Topic: submodular   Node: 9aa3c64a2b88

Provenance: helper lemma. sanity check of multilinear_extension

The multilinear extension agrees with f on indicator vectors: F(1_S) = f(S).
-/

theorem multilinear_extension_indicator {m : ℕ} (f : Finset (Fin m) → ℝ) (S : Finset (Fin m)) :
    multilinear_extension f (finset_indicator_vec S) = f S := by
  dsimp [multilinear_extension]
  rw [Finset.sum_eq_single_of_mem S (Finset.mem_univ S)]
  · have h1 : (∏ u ∈ S, finset_indicator_vec S u) = 1 := by
      apply Finset.prod_eq_one
      intro u hu
      dsimp [finset_indicator_vec]
      rw [if_pos hu]
    have h2 : (∏ u ∈ Sᶜ, (1 - finset_indicator_vec S u)) = 1 := by
      apply Finset.prod_eq_one
      intro u hu
      have hu' : u ∉ S := by
        rw [Finset.mem_compl] at hu
        exact hu
      dsimp [finset_indicator_vec]
      rw [if_neg hu']
      ring
    rw [h1, h2, mul_one, mul_one]
  · intro T _ hne
    have hdisj : (∃ u ∈ T, u ∉ S) ∨ (∃ u ∈ S, u ∉ T) := by
      by_contra! h
      rcases h with ⟨h1, h2⟩
      exact hne (Finset.Subset.antisymm h1 h2)
    cases hdisj with
    | inl h1 =>
      rcases h1 with ⟨u, huT, huS⟩
      have hzero : ∏ u ∈ T, finset_indicator_vec S u = 0 := by
        apply Finset.prod_eq_zero huT
        dsimp [finset_indicator_vec]
        rw [if_neg huS]
      rw [hzero, mul_zero, zero_mul]
    | inr h2 =>
      rcases h2 with ⟨u, huS, huT⟩
      have hucompl : u ∈ Tᶜ := by
        rw [Finset.mem_compl]
        exact huT
      have hzero : ∏ u ∈ Tᶜ, (1 - finset_indicator_vec S u) = 0 := by
        apply Finset.prod_eq_zero hucompl
        dsimp [finset_indicator_vec]
        rw [if_pos huS]
        ring
      rw [hzero, mul_zero]
