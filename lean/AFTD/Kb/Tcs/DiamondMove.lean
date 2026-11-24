import AFTD.Prelude
import AFTD.Kb.Tcs.MaximalChainLowerSet
import AFTD.Kb.Tcs.DiffersInOnePosition
import AFTD.Kb.Tcs.ChainStepElement

/-!
# diamond_move

Topic: combinatorics   Node: 3b2a48b0f1d8

Provenance: formalization of a published result. Source: arXiv:2611.26888 Definition 2.2

Given a finite partially ordered set P, a labeling l : P → Fin (Fintype.card P), and maximal chains of order ideals M and M' of type MaximalChainLowerSet P, diamond_move l M M' holds if there exists an index i : Fin (Fintype.card P) with hi : i.val + 1 < Fintype.card P such that M and M' differ in one position at index ⟨i.val + 1, hi⟩, and there exist elements x y : P such that chain_step_element M i x, chain_step_element M ⟨i.val + 1, hi⟩ y, and l x < l y.
-/

/-- A diamond move between maximal chains of order ideals in J(P) under a linear extension. -/
def diamond_move {P : Type*} [PartialOrder P] [Fintype P]
    (l : P → Fin (Fintype.card P)) (M M' : MaximalChainLowerSet P) : Prop := ∃ (i : Fin (Fintype.card P)) (hi : i.val + 1 < Fintype.card P),
    differs_in_one_position M M' ⟨i.val + 1, by omega⟩ ∧
    ∃ x y : P, chain_step_element M i x ∧
      chain_step_element M ⟨i.val + 1, hi⟩ y ∧ l x < l y
