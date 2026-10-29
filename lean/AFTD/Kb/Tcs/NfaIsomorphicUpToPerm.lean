import AFTD.Prelude

/-!
# nfa_isomorphic_up_to_perm

Topic: automata   Node: 8d3a59cbee39

Provenance: original. Related work: arXiv:2610.08525, Stronger bounds on the degree of ambiguity of finite automata

Two NFAs M₁ and M₂ over alphabet α with state sets σ₁ and σ₂ are isomorphic up to state bijection and alphabet permutation if there exist a state bijection e : σ₁ ≃ σ₂ and a permutation π of the alphabet such that e preserves initial states, accepting states, and transitions with respect to π.
-/

/-- Two NFAs are isomorphic up to state bijection and alphabet permutation. -/
def nfa_isomorphic_up_to_perm {α σ₁ σ₂ : Type*} (M₁ : NFA α σ₁) (M₂ : NFA α σ₂) : Prop := ∃ (e : σ₁ ≃ σ₂) (π : Equiv.Perm α),
    (∀ s, s ∈ M₁.start ↔ e s ∈ M₂.start) ∧
    (∀ s, s ∈ M₁.accept ↔ e s ∈ M₂.accept) ∧
    (∀ s t a, t ∈ M₁.step s a ↔ e t ∈ M₂.step (e s) (π a))
