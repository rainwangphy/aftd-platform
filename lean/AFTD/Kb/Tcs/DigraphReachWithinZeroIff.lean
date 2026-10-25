import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphReachWithin

/-!
# digraph_reach_within_zero_iff

Topic: graphs   Node: fd298c73b825

Provenance: helper lemma. sanity lemma for digraph_reach_within

Sanity: a directed walk of length at most 0 from u to v exists iff u = v.
-/

theorem digraph_reach_within_zero_iff {V : Type*} (D : Digraph V) (u v : V) :
    digraph_reach_within D 0 u v ↔ u = v := Iff.rfl
