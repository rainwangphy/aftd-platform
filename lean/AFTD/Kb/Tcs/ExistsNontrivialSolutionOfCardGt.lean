import AFTD.Prelude

/-!
# exists_nontrivial_solution_of_card_gt

Topic: combinatorics   Node: 298cf8133106

Provenance: helper lemma. arXiv:2610.26686 Lemma 3 proof

If a finite set V has cardinality strictly greater than d, then for any d functions p_j : U -> ℚ, there exists a non-zero function h : V -> ℚ such that ∑_{x ∈ V} h(x) p_j(x) = 0 for all j in Fin d.
-/

/-- A homogeneous system of d equations in more than d unknowns over ℚ has a non-trivial solution. -/
theorem exists_nontrivial_solution_of_card_gt {U : Type*} (V : Finset U) (d : ℕ)
    (p : Fin d → U → ℚ) (hcard : d < V.card) :
    ∃ h : V → ℚ, h ≠ 0 ∧ ∀ j : Fin d, ∑ x : V, h x * p j x = 0 := by
  let L : (V → ℚ) →ₗ[ℚ] (Fin d → ℚ) := {
    toFun := fun h j => ∑ x : V, h x * p j x
    map_add' := fun h1 h2 => by
      ext j
      simp only [Pi.add_apply]
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _
      ring
    map_smul' := fun c h => by
      ext j
      simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      ring
  }
  have hdim : Module.finrank ℚ (Fin d → ℚ) < Module.finrank ℚ (V → ℚ) := by
    simp [hcard]
  have hker : LinearMap.ker L ≠ ⊥ := LinearMap.ker_ne_bot_of_finrank_lt hdim
  rw [Submodule.ne_bot_iff] at hker
  rcases hker with ⟨h, h_mem, h_ne⟩
  rw [LinearMap.mem_ker] at h_mem
  refine ⟨h, h_ne, fun j => ?_⟩
  have hj := congr_fun h_mem j
  exact hj
