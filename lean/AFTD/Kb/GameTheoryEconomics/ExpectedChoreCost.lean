import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.RandomizedOnlineChoreAlgorithm
import AFTD.Kb.GameTheoryEconomics.DeterministicOnlineChoreRule
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.AdditiveValuation

/-!
# expected_chore_cost

Topic: fair_division   Node: 8371cc2cdfc7

Provenance: formalization of a published result. Source: arXiv:2611.00432 Sec 2 & 4

The expected cost of agent i : Fin n at horizon m : ℕ under a randomized online chore algorithm alg : RandomizedOnlineChoreAlgorithm n for arrival costs c : Fin n → ℕ → ℝ, defined as the infinite sum over ω : alg.Ω of (alg.dist ω).toReal * additive_valuation (fun d => c i d.val) (bundle_of ((alg.rule ω).alloc c m) i).
-/

/-- The expected cost of agent i under a randomized online chore algorithm at step m. -/
noncomputable def expected_chore_cost {n : ℕ} (alg : RandomizedOnlineChoreAlgorithm n)
    (c : Fin n → ℕ → ℝ) (m : ℕ) (i : Fin n) : ℝ :=
  ∑' ω : alg.Ω, (alg.dist ω).toReal *
    additive_valuation (fun (d : Fin m) => c i d.val) (bundle_of ((alg.rule ω).alloc c m) i)
