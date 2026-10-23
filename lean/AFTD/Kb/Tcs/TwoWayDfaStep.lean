import AFTD.Prelude
import AFTD.Kb.Tcs.TwoWayDfa

/-!
# two_way_dfa_step

Topic: automata   Node: c02ef03a1857

Provenance: formalization of a published result. Source: arXiv:2610.18897 (A factor-two lower bound for complementing two-way deterministic finite automata), Section 2.1: the tape positions 0, ..., t+1 with endmarkers at 0 and t+1, and the moves

One step on the input w: in configuration (q, i), at position 0 (left endmarker) apply δL and move to 1, at position |w|+1 (right endmarker) apply δR and move to |w|, and at a position 1 ≤ i ≤ |w| read the symbol w_i and move by the direction δ gives. None when the transition is undefined.
-/

def two_way_dfa_step {σ Q : Type*} (A : two_way_dfa σ Q) (w : List σ) (c : Q × ℕ) : Option (Q × ℕ) :=
  if c.2 = 0 then (A.δL c.1).map (fun q => (q, 1))
  else if c.2 = w.length + 1 then (A.δR c.1).map (fun q => (q, w.length))
  else (w[c.2 - 1]?).bind (fun a =>
    (A.δ c.1 a).map (fun r => (r.1, if r.2 then c.2 + 1 else c.2 - 1)))
