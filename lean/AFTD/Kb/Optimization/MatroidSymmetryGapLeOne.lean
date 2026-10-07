import AFTD.Prelude
import AFTD.Kb.Optimization.MultilinearExtension
import AFTD.Kb.Optimization.PermGroupSymmetrize
import AFTD.Kb.Optimization.MatroidPolytope
import AFTD.Kb.Optimization.IsStronglySymmetricInstance
import AFTD.Kb.Optimization.FinsetIndicatorVec

/-!
# matroid_symmetry_gap_le_one

Topic: submodular   Node: 153466b26772

Provenance: formalization of a published result. Source: arXiv:2610.07387 (Stronger hardness for submodular maximization subject to a matroid constraint), Definition 2.2 (implicit there: x̄ ∈ P(M) because G preserves independence and P(M) is convex)

For every strongly symmetric instance max{f(S) : S independent in M} with respect to a permutation group G, the best symmetrized fractional value is at most the best fractional value: max_{x∈P(M)} F(x̄) ≤ max_{x∈P(M)} F(x), i.e. the symmetry gap is at most 1.
-/

theorem matroid_symmetry_gap_le_one {m : ℕ} (M : Matroid (Fin m)) (f : Finset (Fin m) → ℝ)
    (G : Subgroup (Equiv.Perm (Fin m)))
    (hs : is_strongly_symmetric_instance M f G) :
    sSup ((fun x => multilinear_extension f (perm_group_symmetrize G x)) '' matroid_polytope M) ≤
      sSup (multilinear_extension f '' matroid_polytope M) := by
  classical
  set V : Set (Fin m → ℝ) := {x | ∃ S : Finset (Fin m), M.Indep ↑S ∧ x = finset_indicator_vec S}
    with hV
  have hVfin : V.Finite :=
    (Set.finite_range (fun S : Finset (Fin m) => finset_indicator_vec S)).subset
      (by rintro x ⟨S, -, rfl⟩; exact ⟨S, rfl⟩)
  have hPc : IsCompact (matroid_polytope M) := hVfin.isCompact_convexHull (𝕜 := ℝ)
  have hF : Continuous (multilinear_extension f) := by
    unfold multilinear_extension; fun_prop
  have hbdd : BddAbove (multilinear_extension f '' matroid_polytope M) :=
    (hPc.image hF).bddAbove
  have hne : (matroid_polytope M).Nonempty :=
    ⟨finset_indicator_vec ∅, subset_convexHull ℝ _ ⟨∅, by simpa using M.empty_indep, rfl⟩⟩
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
      simp only [Finset.coe_filter, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
        true_and] at hτ ⊢
      exact G.mul_mem hτ hσ
    · intro τ hτ
      simp only [Finset.coe_filter, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ,
        true_and] at hτ ⊢
      exact G.mul_mem hτ (G.inv_mem hσ)
    · intro τ _; simp
    · intro τ _; simp
    · intro τ _; simp [mul_inv_rev, Equiv.Perm.mul_apply]
  have hσV : ∀ σ ∈ G, ∀ x ∈ V, (fun u => x (σ⁻¹ u)) ∈ V := by
    rintro σ hσ _ ⟨S, hS, rfl⟩
    refine ⟨S.map σ.toEmbedding, ?_, hact_ind σ S⟩
    exact (hs.2 _ _ (hsymσ σ hσ S)).2 hS
  have hσP : ∀ σ ∈ G, ∀ x ∈ matroid_polytope M, (fun u => x (σ⁻¹ u)) ∈ matroid_polytope M := by
    intro σ hσ x hx
    have h1 : (fun u => x (σ⁻¹ u)) ∈ (LinearMap.funLeft ℝ ℝ ⇑σ⁻¹) '' matroid_polytope M :=
      ⟨x, hx, rfl⟩
    rw [matroid_polytope, LinearMap.image_convexHull] at h1
    refine convexHull_mono ?_ h1
    rintro _ ⟨y, hy, rfl⟩
    exact hσV σ hσ y hy
  have hsymP : ∀ x ∈ matroid_polytope M, perm_group_symmetrize G x ∈ matroid_polytope M := by
    intro x hx
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
  refine csSup_le_csSup hbdd (hne.image _) ?_
  rintro _ ⟨x, hx, rfl⟩
  exact ⟨_, hsymP x hx, rfl⟩
