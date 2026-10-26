import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsEjrCommittee
import AFTD.Kb.GameTheoryEconomics.EjrChainOfNestedCommittees

/-!
# ejr_chain_nested_committees_iff

Topic: social_choice   Node: e8ae1f19588b

Provenance: helper lemma. step towards ejr_committee_monotone_chain_exists

An approval profile admits an EJR committee chain if and only if it admits an increasing sequence of EJR committees of sizes 0 through m.
-/

/-- An approval profile admits an EJR committee chain if and only if it admits an increasing sequence of EJR committees of sizes 0 through m. -/
theorem ejr_chain_nested_committees_iff {n m : ℕ} (A : Fin n → Finset (Fin m)) :
    (∃ σ : Equiv.Perm (Fin m), ∀ k, k ≤ m →
        is_ejr_committee A k (Finset.univ.filter fun c => (σ c : ℕ) < k)) ↔
      (∃ W : ℕ → Finset (Fin m), W 0 = ∅ ∧
        (∀ k, k < m → W k ⊆ W (k + 1)) ∧
        (∀ k, k ≤ m → is_ejr_committee A k (W k))) := by
  constructor
  · rintro ⟨σ, hσ⟩
    refine ⟨fun k => Finset.univ.filter fun c => (σ c : ℕ) < k, ?_, ?_, ?_⟩
    · simp
    · intro k _ c hc
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
      omega
    · intro k hk
      exact hσ k hk
  · exact ejr_chain_of_nested_committees A
