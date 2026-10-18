import AFTD.Prelude
import AFTD.Kb.Optimization.PermGroupSymmetrize

/-!
# perm_group_symmetrize_idempotent

Topic: submodular   Node: 8c47e5906b40

Provenance: helper lemma. step towards matroid_symmetry_gap_lt_eight_seventeenths

Symmetrization is idempotent: symmetrizing twice is the same as symmetrizing once, i.e. x̄ is fixed by every element of G.
-/

/-- The group average of a group average is the group average: symmetrization is idempotent. -/
theorem perm_group_symmetrize_idempotent {m : ℕ} (G : Subgroup (Equiv.Perm (Fin m)))
    (x : Fin m → ℝ) :
    perm_group_symmetrize G (perm_group_symmetrize G x) = perm_group_symmetrize G x := by
  classical
  have hinv : ∀ {σ : Equiv.Perm (Fin m)} (hσ : σ ∈ G) (u : Fin m),
      perm_group_symmetrize G x (σ⁻¹ u) = perm_group_symmetrize G x u := by
    intro σ hσ u
    unfold perm_group_symmetrize
    congr 1
    refine Finset.sum_nbij' (fun τ => σ * τ) (fun τ => σ⁻¹ * τ) ?_ ?_ ?_ ?_ ?_
    · intro τ hτ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
      exact G.mul_mem hσ hτ
    · intro τ hτ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hτ ⊢
      exact G.mul_mem (G.inv_mem hσ) hτ
    · intro τ _; simp
    · intro τ _; simp
    · intro τ _
      simp [mul_inv_rev, Equiv.Perm.mul_apply]
  funext u
  show (∑ σ ∈ Finset.univ.filter (· ∈ G), perm_group_symmetrize G x (σ⁻¹ u)) /
      ((Finset.univ.filter (· ∈ G)).card : ℝ) = perm_group_symmetrize G x u
  have h_eq : ∀ σ ∈ Finset.univ.filter (· ∈ G),
      perm_group_symmetrize G x (σ⁻¹ u) = perm_group_symmetrize G x u := by
    intro σ hσ
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hσ
    exact hinv hσ u
  rw [Finset.sum_congr rfl h_eq]
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : ((Finset.univ.filter (· ∈ G)).card : ℝ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Finset.card_ne_zero.mpr
      ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_univ 1, G.one_mem⟩⟩
  exact mul_div_cancel_left₀ _ hcard
