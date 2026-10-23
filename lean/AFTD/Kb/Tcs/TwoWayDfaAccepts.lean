import AFTD.Prelude
import AFTD.Kb.Tcs.TwoWayDfa
import AFTD.Kb.Tcs.TwoWayDfaRun

/-!
# two_way_dfa_accepts

Topic: automata   Node: ce0418c555ad

Provenance: formalization of a published result. Source: arXiv:2610.18897 (A factor-two lower bound for complementing two-way deterministic finite automata), Section 2.1: acceptance exactly upon reaching (f, 0)

A accepts w when its computation from (s, 0) reaches the configuration (f, 0) (state f on the left endmarker). Infinite computations and halting elsewhere reject.
-/

def two_way_dfa_accepts {σ Q : Type*} (A : two_way_dfa σ Q) (w : List σ) : Prop :=
  ∃ t, two_way_dfa_run A w t = some (A.f, 0)
