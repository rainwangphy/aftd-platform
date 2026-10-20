import AFTD.Prelude
import AFTD.Kb.Tcs.NfaTransitionGraph
import AFTD.Kb.Tcs.SimpleGraphIsCactus

/-!
# is_bipartite_cactus_nfa

Topic: automata   Node: 4dfc184c58ea

Provenance: formalization of a published result. Source: arXiv:2610.11717 Thm 1.1

An NFA A is a bipartite cactus automaton if its undirected transition graph is a cactus and 2-colorable.
-/

/-- Predicate asserting that an NFA has a bipartite cactus transition graph. -/
def is_bipartite_cactus_nfa {α σ : Type*} (A : NFA α σ) : Prop := simple_graph_is_cactus (nfa_transition_graph A) ∧ (nfa_transition_graph A).Colorable 2
