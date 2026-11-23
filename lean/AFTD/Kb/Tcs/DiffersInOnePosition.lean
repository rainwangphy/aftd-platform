import AFTD.Prelude
import AFTD.Kb.Tcs.MaximalChainLowerSet

/-!
# differs_in_one_position

Topic: combinatorics   Node: f52b8854365c

Provenance: formalization of a published result. Source: arXiv:2611.26888 Section 2.2

Two maximal chains M and M' in J(P) differ in position j if their j-th elements are distinct and all other elements agree.
-/

/-- Two maximal chains differ in exactly one position j. -/
def differs_in_one_position {P : Type*} [PartialOrder P] [Fintype P]
    (M M' : MaximalChainLowerSet P) (j : Fin (Fintype.card P + 1)) : Prop := M.chain j ≠ M'.chain j ∧ ∀ k : Fin (Fintype.card P + 1), k ≠ j → M.chain k = M'.chain k
