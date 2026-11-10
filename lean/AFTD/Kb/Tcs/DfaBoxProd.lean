import AFTD.Prelude

/-!
# dfa_box_prod

Topic: automata   Node: 60e8c573e105

Provenance: formalization of a published result. Source: arXiv:2611.09136 Section 2

The sequential two-tape product automaton (box product) of two DFAs A₁ and A₂ with disjoint input alphabets has state type σ₁ × σ₂, input alphabet α₁ ⊕ α₂, start state (A₁.start, A₂.start), accepting states A₁.accept ×ˢ A₂.accept, and transitions δ((q₁, q₂), inl a₁) = (A₁.step q₁ a₁, q₂) and δ((q₁, q₂), inr a₂) = (q₁, A₂.step q₂ a₂).
-/

/-- The sequential two-tape product automaton (box product) of two DFAs with disjoint input alphabets. -/
def dfa_box_prod {α₁ α₂ σ₁ σ₂ : Type*} (A₁ : DFA α₁ σ₁) (A₂ : DFA α₂ σ₂) :
    DFA (Sum α₁ α₂) (σ₁ × σ₂) :=
  ⟨fun (q₁, q₂) a =>
    match a with
    | Sum.inl a₁ => (A₁.step q₁ a₁, q₂)
    | Sum.inr a₂ => (q₁, A₂.step q₂ a₂),
   (A₁.start, A₂.start),
   { p | p.1 ∈ A₁.accept ∧ p.2 ∈ A₂.accept }⟩
