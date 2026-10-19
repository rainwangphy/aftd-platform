import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleValuation
import AFTD.Kb.GameTheoryEconomics.SocialChoiceFairDivisionIndivisibleAllocation

/-!
# is_alpha_ef1

Topic: fair_division   Node: bab37ebab237

Provenance: formalization of a published result. Source: arXiv:2610.23686 (Revisiting the Fairness of Pure Nash Equilibria of Round-Robin), Definition 1

For α in [0,1], an allocation is α-EF1 if for every pair of agents i ≠ j with A_j nonempty there is a good g in A_j with v_i(A_i) ≥ α · v_i(A_j \ {g}).
-/

/-- `α`-EF1 (Definition 1 of arXiv:2610.23686): for all `i ≠ j` with `A j` nonempty, some `g ∈ A j` has `α · v_i(A_j \ {g}) ≤ v_i(A_i)`. -/
def is_alpha_ef1 {N G : Type*} [DecidableEq G] (α : ℝ)
    (v : SocialChoice.FairDivision.Indivisible.Valuation N G)
    (A : SocialChoice.FairDivision.Indivisible.Allocation N G) : Prop :=
  ∀ i j : N, i ≠ j → (A j).Nonempty → ∃ g ∈ A j, α * v.val i (A j \ {g}) ≤ v.val i (A i)
