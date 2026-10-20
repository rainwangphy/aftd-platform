import AFTD.Prelude

/-!
# nfa_transition_graph

Topic: automata   Node: c5115437aa9a

Provenance: formalization of a published result. Source: arXiv:2610.11717 Sec. 2

The transition graph of an NFA A has an undirected edge between distinct states u and v if there is a transition from u to v or from v to u on some input symbol.
-/

/-- The undirected transition graph G(A) of an NFA A without loops or multiple edges. -/
def nfa_transition_graph {α σ : Type*} (A : NFA α σ) : SimpleGraph σ := SimpleGraph.fromRel (fun u v => ∃ a : α, v ∈ A.step u a)
