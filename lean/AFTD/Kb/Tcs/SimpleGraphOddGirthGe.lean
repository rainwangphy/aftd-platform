import AFTD.Prelude

/-!
# simple_graph_odd_girth_ge

Topic: graphs   Node: d4e16335dcdc

Provenance: formalization of a published result. Source: arXiv:2611.05178 Question 5.5

A simple graph G has odd girth at least k if every cycle in G of odd length has length at least k.
-/

/-- A simple graph G has odd girth at least k if every cycle of odd length has length at least k. -/
def simple_graph_odd_girth_ge {V : Type*} (G : SimpleGraph V) (k : ℕ) : Prop := ∀ (u : V) (w : G.Walk u u), w.IsCycle → Odd w.length → k ≤ w.length
