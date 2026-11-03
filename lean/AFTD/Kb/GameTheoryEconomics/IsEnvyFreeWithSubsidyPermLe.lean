import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.IsEnvyFreeWithSubsidy

/-!
# is_envy_free_with_subsidy_perm_le

Topic: fair_division   Node: bb578abdb7c1

Provenance: helper lemma. step towards scaled_common_ratio_bivalued_efx_fpo_envyfreeable

If (σ, p) is envy-free with subsidies, then for every permutation π of agents, ∑_i v_i(A_{π(i)}) ≤ ∑_i v_i(A_i).
-/

/-- If an allocation is envy-free with subsidies, then for every permutation of the agents, the sum of values for the permuted bundles is at most the sum of values for their own bundles. -/
theorem is_envy_free_with_subsidy_perm_le {m n : ℕ}
    (v : Fin n → Finset (Fin m) → ℝ) (σ : Fin m → Fin n) (p : Fin n → ℝ)
    (hef : is_envy_free_with_subsidy v σ p) (π : Equiv.Perm (Fin n)) :
    ∑ i, v i (bundle_of σ (π i)) ≤ ∑ i, v i (bundle_of σ i) := by
  have h := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hef.2 i (π i))
  simp only [Finset.sum_add_distrib] at h
  rw [Equiv.sum_comp π p] at h
  linarith
