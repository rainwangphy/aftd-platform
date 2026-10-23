import AFTD.Prelude
import AFTD.Kb.Tcs.TwoWayDfa

/-!
# two_way_dfa_direction_determinate

Topic: automata   Node: 8c4472d5878e

Provenance: formalization of a published result. Source: arXiv:2610.18897 (A factor-two lower bound for complementing two-way deterministic finite automata), Section 7.1: direction-determinate sources

A is direction-determinate: some d : Q → {left, right} gives the direction of every defined transition from the state it enters, endmarker transitions included.
-/

def two_way_dfa_direction_determinate {σ Q : Type*} (A : two_way_dfa σ Q) : Prop :=
  ∃ d : Q → Bool, (∀ p a q e, A.δ p a = some (q, e) → e = d q) ∧
    (∀ p q, A.δL p = some q → d q = true) ∧ (∀ p q, A.δR p = some q → d q = false)
