import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Ef1costPairOk

/-!
# ef1cost_stage

Topic: fair_division   Node: 734802915641

A stage of the greedy transfer: `S` (moved from the complement of `X`) still leaves the donor non-EF1, and every moved item has cost ratio `u/v` at most that of every remaining one.
-/

/-- A stage of the greedy transfer: `S` (moved from the complement of `X`) still leaves the donor non-EF1, and every moved item has cost ratio `u/v` at most that of every remaining one. -/
def ef1cost_stage {m : ℕ} (u v : Fin m → ℝ) (X S : Finset (Fin m)) : Prop :=
  S ⊆ Xᶜ ∧ ¬ ef1cost_pair_ok v (Xᶜ \ S) (X ∪ S) ∧
    ∀ e ∈ S, ∀ f ∈ Xᶜ \ S, u e * v f ≤ u f * v e
