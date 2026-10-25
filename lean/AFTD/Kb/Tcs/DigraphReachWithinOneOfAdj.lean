import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphReachWithin

/-!
# digraph_reach_within_one_of_adj

Topic: graphs   Node: f2bde1b13953

Provenance: helper lemma. sanity lemma for digraph_reach_within

Sanity: an arc u -> v is a directed walk of length at most 1 from u to v.
-/

theorem digraph_reach_within_one_of_adj {V : Type*} (D : Digraph V) (u v : V) (h : D.Adj u v) :
    digraph_reach_within D 1 u v := Or.inr ⟨v, h, rfl⟩
