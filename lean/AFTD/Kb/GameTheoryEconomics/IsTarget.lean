import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Charity

/-!
# is_target

Topic: fair_division   Node: c27dd7e764fe

Provenance: formalization of a published result. Source: arXiv:2611.34488, Section 2

Given an allocation A of goods in Fin m to n agents, a bundle D is a target for agent i if D is the allocated bundle A j of another agent j ≠ i, or D is the charity of unallocated goods.
-/

/-- A target for agent i is either another agent j's bundle or the charity of unallocated goods. -/
def is_target {m n : ℕ} (A : Fin n → Finset (Fin m)) (i : Fin n) (D : Finset (Fin m)) : Prop := (∃ j : Fin n, j ≠ i ∧ D = A j) ∨ D = charity A
