import AFTD.Prelude

/-!
# digraph_reach_within

Topic: graphs   Node: 5abca5d3fd98

Provenance: formalization of a published result. Source: arXiv:2610.09648 (An asymptotically tight bound on oriented diameter), Section 1: the directed distance dist(x,y) of an orientation (length of a shortest directed x-y path); this predicate says dist(x,y) <= k.

digraph_reach_within D k u v: there is a directed walk of length at most k from u to v in the digraph D (equivalently, the directed distance from u to v is at most k). For k = 0 it means u = v; for k + 1 either a walk of length at most k exists or u has an out-neighbour w with a walk of length at most k from w to v.
-/

def digraph_reach_within {V : Type*} (D : Digraph V) : ℕ → V → V → Prop
  | 0, u, v => u = v
  | k + 1, u, v => digraph_reach_within D k u v ∨ ∃ w, D.Adj u w ∧ digraph_reach_within D k w v
