import AFTD.Prelude

/-!
# nfa_is_trim

Topic: automata   Node: ab40438b1d08

Provenance: formalization of a published result. Source: arXiv:2610.08525 Sec. 2

An NFA M is trim if every state q is reachable from the start states by some word and co-reachable (can reach an accept state by some word).
-/

/-- An NFA is trim if every state is reachable from the start states and co-reachable to an accept state. -/
def nfa_is_trim {α σ : Type*} (M : NFA α σ) : Prop :=
  ∀ (q : σ), (∃ (w : List α), q ∈ M.evalFrom M.start w) ∧
             (∃ (w : List α) (t : σ), t ∈ M.accept ∧ t ∈ M.evalFrom {q} w)
