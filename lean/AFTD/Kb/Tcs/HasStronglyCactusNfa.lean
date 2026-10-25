import AFTD.Prelude
import AFTD.Kb.Tcs.StronglyCactusNfa

/-!
# has_strongly_cactus_nfa

Topic: automata   Node: c7091baa74a0

Provenance: helper lemma. step towards regular_language_has_bipartite_cactus_nfa

A language L has a strongly cactus NFA of parity p when there are a finite state type σ, an NFA A over σ, and a state s such that A accepts exactly L and A is strongly cactus of parity p with initial state s.
-/

/-- A language is representable by a finite-state strongly cactus automaton of parity `p` with a distinguished initial state. This is the induction invariant of the paper's Theorem 3.8. -/
def has_strongly_cactus_nfa {α : Type*} (L : Language α) (p : ZMod 2) : Prop := (∃ (σ : Type) (_ : Fintype σ) (A : NFA α σ) (s : σ), A.accepts = L ∧ strongly_cactus_nfa A s p)
