import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation

/-!
# knapsack_opt

Topic: fair_division   Node: 1ef1128a40ec

Provenance: formalization of a published result. Source: arXiv:2611.12740 Section 3.1

For an item subset C and budget b, OPT(C) is the maximum additive value v(S) over all subsets S ⊆ C with total size s(S) ≤ b.
-/

/-- The optimal knapsack value an agent can obtain from item set C within budget b. -/
noncomputable def knapsack_opt {m : ℕ} (v : Fin m → ℝ) (s : Fin m → ℝ) (b : ℝ)
    (C : Finset (Fin m)) : ℝ := ⨆ (S : {S : Finset (Fin m) // S ⊆ C ∧ additive_valuation s S ≤ b}), additive_valuation v S.val
