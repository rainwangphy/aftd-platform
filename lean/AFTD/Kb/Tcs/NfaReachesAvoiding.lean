import AFTD.Prelude
import AFTD.Kb.Tcs.NfaTransitionGraph

/-!
# nfa_reaches_avoiding

Topic: automata   Node: 9e9572901d48

Provenance: helper lemma. step towards regular_language_has_bipartite_cactus_nfa

Two states u, v of an NFA A are connected inside the transition graph with the initial state s deleted when some walk from u to v avoids s at every vertex.
-/

/-- Walks of the transition graph from `u` to `v` that avoid the distinguished state `s`; this is the formal stand-in for "u and v lie in the same component of G(A) - s". -/
def nfa_reaches_avoiding {α σ : Type*} (A : NFA α σ) (s u v : σ) : Prop := ∃ w : (nfa_transition_graph A).Walk u v, ∀ x ∈ w.support, x ≠ s
