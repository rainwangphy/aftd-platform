import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BundleRemoveKValue
import AFTD.Kb.GameTheoryEconomics.BundleOf

/-!
# is_alpha_efk_allocation

Topic: fair_division   Node: 363db4342348

Provenance: formalization of a published result. Source: arXiv:2610.34625, Section 2.1

An allocation σ : Fin m → Fin n of m goods among n agents is α-EFk under valuations v : Fin n → Finset (Fin m) → ℝ if for all distinct agents i and j, agent i values her bundle at least α times the value of j's bundle after removing the k most valuable goods for agent i.
-/

/-- An allocation σ is α-EFk if for all distinct agents i and j, agent i values her bundle at least α times the value of j's bundle after removing the k most valuable goods for i. -/
def is_alpha_efk_allocation {m n : ℕ} (v : Fin n → Finset (Fin m) → ℝ) (α : ℝ) (k : ℕ) (σ : Fin m → Fin n) : Prop :=
  ∀ (i j : Fin n), i ≠ j → α * bundle_remove_k_value (v i) k (bundle_of σ j) ≤ v i (bundle_of σ i)
