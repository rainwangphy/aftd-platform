import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsUpgradeFeasible

/-!
# has_upgrade_recourse

Topic: fair_division   Node: 621bb1798ab1

Provenance: formalization of a published result. Source: arXiv:2611.00432, Definition 2.1

An online chore allocation sequence A : ∀ m : ℕ, Fin m → Fin n for n agents has upgrade recourse with respect to chore costs c : Fin n → ℕ → ℝ if for every arrival m : ℕ, the update from allocation A m to A (m + 1) is upgrade-feasible (is_upgrade_feasible) under the costs fun i (d : Fin (m + 1)) => c i d.val.
-/

/-- An online chore allocation algorithm has upgrade recourse if every single-arrival update is upgrade-feasible. -/
def has_upgrade_recourse (n : ℕ) (c : Fin n → ℕ → ℝ) (A : ∀ m : ℕ, Fin m → Fin n) : Prop := ∀ m : ℕ, is_upgrade_feasible (fun i d => c i d.val) (A m) (A (m + 1))
