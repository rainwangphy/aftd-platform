import AFTD.Prelude
import AFTD.Kb.Tcs.NfaReachesAvoiding
import AFTD.Kb.Tcs.SimpleGraphIsCactus
import AFTD.Kb.Tcs.NfaTransitionGraph

/-!
# strongly_cactus_nfa

Topic: automata   Node: 67953a6a2877

Provenance: helper lemma. step towards regular_language_has_bipartite_cactus_nfa

An NFA A is a strongly cactus automaton of parity p with initial state s when: s is the only start state and no transition enters s; the transition graph is a cactus with a transition-compatible colouring that gives s colour 0 and every accepting state colour p; every component of G(A) - s has at most one entry state and contains an accepting state; and every state that is the source of a transition into an accepting state is joined to s by a unique path.
-/

/-- The paper's "strongly cactus automaton of parity p" (Definition 3.2): the initial state is the single start state and no transition enters it, the transition graph is a cactus and 2-coloured by a transition-compatible `χ` with `χ s = 0` and `χ f = p` for accepting `f`, every component of `G(A) - s` (read as: all states other than `s`, grouped by `nfa_reaches_avoiding`) has at most one entry state and contains an accepting state, and every possible source of a last transition off the initial state is joined to `s` by a unique path.

This is the invariant that the paper's Section 3 constructions preserve; it is what makes the Kleene-star construction work. -/
def strongly_cactus_nfa {α σ : Type*} (A : NFA α σ) (s : σ) (p : ZMod 2) : Prop := A.start = {s} ∧
  simple_graph_is_cactus (nfa_transition_graph A) ∧
  (∀ (q : σ) (a : α), s ∉ A.step q a) ∧
  (∀ q : σ, Nonempty ((nfa_transition_graph A).Walk s q)) ∧
  (∃ χ : σ → ZMod 2, χ s = 0 ∧
    (∀ (q : σ) (a : α) (r : σ), r ∈ A.step q a → χ r = χ q + 1) ∧
    (∀ f : σ, f ∈ A.accept → χ f = p)) ∧
  (∀ (t₁ t₂ : σ), t₁ ≠ s → t₂ ≠ s → (∃ a : α, t₁ ∈ A.step s a) → (∃ a : α, t₂ ∈ A.step s a) →
    (∃ u : σ, nfa_reaches_avoiding A s t₁ u ∧ nfa_reaches_avoiding A s t₂ u) → t₁ = t₂) ∧
  (∀ u : σ, u ≠ s → ∃ f : σ, f ∈ A.accept ∧ nfa_reaches_avoiding A s u f) ∧
  (∀ g : σ, g ≠ s → (∃ (a : α) (f : σ), f ∈ A.accept ∧ f ∈ A.step g a) →
    ∀ (w₁ w₂ : (nfa_transition_graph A).Walk s g), w₁.IsPath → w₂.IsPath → w₁.support = w₂.support)
