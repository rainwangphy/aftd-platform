import AFTD.Prelude

/-!
# nfa_has_singleton_sccs

Topic: automata   Node: 39e90cd19afe

Provenance: original. Related work: arXiv:2610.08525 Section 2

An NFA M has singleton strongly connected components if for all states p and q, whenever q is reachable from {p} by some word and p is reachable from {q} by some word, p = q.
-/

/-- An NFA has singleton strongly connected components if mutual reachability between states is antisymmetric. -/
def nfa_has_singleton_sccs {α σ : Type*} (M : NFA α σ) : Prop := ∀ p q : σ, (∃ w₁, q ∈ M.evalFrom {p} w₁) → (∃ w₂, p ∈ M.evalFrom {q} w₂) → p = q
