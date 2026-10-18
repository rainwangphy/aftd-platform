import AFTD.Prelude
import AFTD.Kb.Optimization.PermGroupSymmetrize

/-!
# sum_perm_group_symmetrize

Topic: submodular   Node: 3e8a75541a88

Provenance: helper lemma. step towards matroid_symmetry_gap_lt_eight_seventeenths

Symmetrization preserves the total mass: the coordinates of x̄ = E_{σ∈G}[σ(x)] sum to the same value as the coordinates of x.
-/

/-- Symmetrization over a permutation group preserves the sum of the coordinates. -/
theorem sum_perm_group_symmetrize {m : ℕ} (G : Subgroup (Equiv.Perm (Fin m)))
    (x : Fin m → ℝ) :
    ∑ u, perm_group_symmetrize G x u = ∑ u, x u := by
  classical
  simp only [perm_group_symmetrize]
  rw [← Finset.sum_div]
  rw [Finset.sum_comm]
  simp only [Equiv.sum_comp]
  rw [Finset.sum_const, nsmul_eq_mul]
  have hcard : ((Finset.univ.filter (· ∈ G)).card : ℝ) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Finset.card_ne_zero.mpr
      ⟨1, Finset.mem_filter.mpr ⟨Finset.mem_univ 1, G.one_mem⟩⟩
  exact mul_div_cancel_left₀ _ hcard
