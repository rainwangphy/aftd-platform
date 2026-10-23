import AFTD.Prelude
import AFTD.Kb.Tcs.TwoWayDfa

/-!
# two_way_dfa_mixed_count

Topic: automata   Node: 80566438eef7

Provenance: formalization of a published result. Source: arXiv:2610.18897 (A factor-two lower bound for complementing two-way deterministic finite automata), Corollary 7.2: the number b of mixed states

b: the number of states that are targets of both a left-moving and a right-moving transition, endmarker transitions included, once the row (f, L) is deleted.
-/

noncomputable def two_way_dfa_mixed_count {σ Q : Type*} (A : two_way_dfa σ Q) : ℕ :=
  {q : Q | ((∃ p a, A.δ p a = some (q, false)) ∨ ∃ p, A.δR p = some q) ∧
    ((∃ p a, A.δ p a = some (q, true)) ∨ ∃ p, p ≠ A.f ∧ A.δL p = some q)}.ncard
