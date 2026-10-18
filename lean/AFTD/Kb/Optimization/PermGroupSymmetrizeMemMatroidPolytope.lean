import AFTD.Prelude
import AFTD.Kb.Optimization.PermGroupSymmetrize
import AFTD.Kb.Optimization.MatroidPolytope
import AFTD.Kb.Optimization.IsStronglySymmetricInstance
import AFTD.Kb.Optimization.FinsetIndicatorVec

/-!
# perm_group_symmetrize_mem_matroid_polytope

Topic: submodular   Node: 9ec4516940d0

Provenance: helper lemma. step towards matroid_symmetry_gap_lt_eight_seventeenths

For a strongly symmetric instance, symmetrizing a point of the matroid polytope stays inside the matroid polytope.
-/

/-- Under strong symmetry the matroid polytope is invariant under symmetrization. -/
theorem perm_group_symmetrize_mem_matroid_polytope {m : ℕ} (M : Matroid (Fin m))
    (f : Finset (Fin m) → ℝ) (G : Subgroup (Equiv.Perm (Fin m)))
    (hs : is_strongly_symmetric_instance M f G) {x : Fin m → ℝ}
    (hx : x ∈ matroid_polytope M) :
    perm_group_symmetrize G x ∈ matroid_polytope M := by
  classical
  set V : Set (Fin m → ℝ) := {x | ∃ S : Finset (Fin m), M.Indep ↑S ∧ x = finset_indicator_vec S}
    with hV
  have hact_ind : ∀ (σ : Equiv.Perm (Fin m)) (S : Finset (Fin m)),
      (fun u => finset_indicator_vec S (σ⁻¹ u)) =
        finset_indicator_vec (S.map σ.toEmbedding) := by
    intro σ S; funext u
    simp [finset_indicator_vec, Finset.mem_map_equiv, Equiv.Perm.inv_def]
  have hsymσ : ∀ σ ∈ G, ∀ S : Finset (Fin m),
      perm_group_symmetrize G (finset_indicator_vec (S.map σ.toEmbedding)) =
        perm_group_symmetrize G (finset_indicator_vec S) := by
    intro σ hσ S
    funext u
    unfold perm_group_symmetrize
    congr 1
    rw [← hact_ind]
    refine Finset.sum_nbij' (fun τ => τ * σ) (fun τ => τ * σ⁻¹) ?_ ?_ ?_ ?_ ?_
    · intro τ hτ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
      exact G.mul_mem hτ hσ
    · intro τ hτ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
      exact G.mul_mem hτ (G.inv_mem hσ)
    · intro τ _; simp
    · intro τ _; simp
    · intro τ _; simp [mul_inv_rev, Equiv.Perm.mul_apply]
  have hσV : ∀ σ ∈ G, ∀ y ∈ V, (fun u => y (σ⁻¹ u)) ∈ V := by
    rintro σ hσ _ ⟨S, hS, rfl⟩
    refine ⟨S.map σ.toEmbedding, ?_, hact_ind σ S⟩
    exact (hs.2 _ _ (hsymσ σ hσ S)).2 hS
  have hσP : ∀ σ ∈ G, ∀ y ∈ matroid_polytope M, (fun u => y (σ⁻¹ u)) ∈ matroid_polytope M := by
    intro σ hσ y hy
    have h1 : (fun u => y (σ⁻¹ u)) ∈ (LinearMap.funLeft ℝ ℝ ⇑σ⁻¹) '' matroid_polytope M :=
      ⟨y, hy, rfl⟩
    rw [matroid_polytope, LinearMap.image_convexHull] at h1
    refine convexHull_mono ?_ h1
    rintro _ ⟨z, hz, rfl⟩
    exact hσV σ hσ z hz
  set T := Finset.univ.filter (· ∈ G) with hT
  have hcard : (0 : ℝ) < T.card := by
    have : (1 : Equiv.Perm (Fin m)) ∈ T := by simp [hT, G.one_mem]
    exact_mod_cast Finset.card_pos.2 ⟨_, this⟩
  have heq : perm_group_symmetrize G x =
      ∑ σ ∈ T, (1 / (T.card : ℝ)) • (fun u => x (σ⁻¹ u)) := by
    funext u
    simp only [perm_group_symmetrize, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hT]
    rw [← Finset.mul_sum, div_eq_inv_mul, one_div]
  rw [heq]
  refine (convex_convexHull ℝ _).sum_mem (fun _ _ => by positivity) ?_ ?_
  · rw [Finset.sum_const, nsmul_eq_mul]; field_simp
  · intro σ hσ
    exact hσP σ (by simpa [hT] using hσ) x hx
