import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation

/-!
# is_alpha_ef1_goods

Topic: fair_division   Node: 2049490fac22

Provenance: formalization of a published result. Source: arXiv:2610.34625 Sec. 2.1

An allocation of m indivisible goods to n agents is alpha-EF1 under additive valuations u if for every pair of distinct agents i and j with j's bundle nonempty, there exists a good g in j's bundle such that alpha times i's value for j's bundle without g is at most i's value for i's own bundle.
-/

/-- An allocation σ is α-EF1 for additive valuations u if for all distinct agents i ≠ j with non-empty bundle A_j, some item g in A_j satisfies α * u_i(A_j \ {g}) ≤ u_i(A_i). -/
def is_alpha_ef1_goods {m n : ℕ} (u : Fin n → Fin m → ℝ) (α : ℝ) (σ : Fin m → Fin n) : Prop :=
  ∀ (i j : Fin n), i ≠ j → (bundle_of σ j).Nonempty →
    ∃ g ∈ bundle_of σ j, α * additive_valuation (u i) ((bundle_of σ j).erase g) ≤
      additive_valuation (u i) (bundle_of σ i)
