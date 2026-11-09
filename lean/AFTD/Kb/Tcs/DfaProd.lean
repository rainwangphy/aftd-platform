import AFTD.Prelude

/-!
# dfa_prod

Topic: automata   Node: 6fc0fe08183d

Provenance: formalization of a published result. Source: arXiv:2611.09136 Section 2

The direct product `dfa_prod A₁ A₂` of two deterministic finite automata `A₁ : DFA α σ₁` and `A₂ : DFA α σ₂` over alphabet `α` is the DFA with state type `σ₁ × σ₂`, start state `(A₁.start, A₂.start)`, transition function `step (q₁, q₂) a = (A₁.step q₁ a, A₂.step q₂ a)`, and accepting states `{p : σ₁ × σ₂ | p.1 ∈ A₁.accept ∧ p.2 ∈ A₂.accept}`.
-/

/-- The direct product of two DFAs over the same alphabet. -/
def dfa_prod {α σ₁ σ₂ : Type*} (A₁ : DFA α σ₁) (A₂ : DFA α σ₂) : DFA α (σ₁ × σ₂) where
  step := fun (q₁, q₂) a => (A₁.step q₁ a, A₂.step q₂ a)
  start := (A₁.start, A₂.start)
  accept := { p | p.1 ∈ A₁.accept ∧ p.2 ∈ A₂.accept }
