import AFTD.Prelude
import AFTD.Kb.Tcs.MaximalChainLowerSet

/-!
# chain_step_element

Topic: combinatorics   Node: 05036e2bca3b

Provenance: formalization of a published result. Source: arXiv:2611.26888 Section 2.2

An element x of P is the step element at index i of a maximal chain M of order ideals if x is not in M_i but is in M_{i+1}.
-/

/-- The unique element of P added at step i of a maximal chain of order ideals. -/
def chain_step_element {P : Type*} [PartialOrder P] [Fintype P]
    (M : MaximalChainLowerSet P) (i : Fin (Fintype.card P)) (x : P) : Prop := x ∉ (M.chain i.castSucc : Set P) ∧ x ∈ (M.chain i.succ : Set P)
