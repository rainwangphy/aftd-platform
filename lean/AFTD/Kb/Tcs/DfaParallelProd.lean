import AFTD.Prelude

/-!
# dfa_parallel_prod

Topic: automata   Node: 76135c1114f2

Provenance: formalization of a published result. Source: arXiv:2611.09136, Section 2

The parallel two-tape product `dfa_parallel_prod A₁ A₂` of two deterministic finite automata `A₁ : DFA α₁ σ₁` and `A₂ : DFA α₂ σ₂` is the DFA with state type `σ₁ × σ₂`, alphabet `α₁ × α₂`, start state `(A₁.start, A₂.start)`, transition function `step (q₁, q₂) (a₁, a₂) = (A₁.step q₁ a₁, A₂.step q₂ a₂)`, and accepting states `{p | p.1 ∈ A₁.accept ∧ p.2 ∈ A₂.accept}`.
-/

/-- Parallel two-tape product of two deterministic finite automata. -/
def dfa_parallel_prod {α₁ α₂ σ₁ σ₂ : Type*} (A₁ : DFA α₁ σ₁) (A₂ : DFA α₂ σ₂) : DFA (α₁ × α₂) (σ₁ × σ₂) where
  step := fun (q₁, q₂) (a₁, a₂) => (A₁.step q₁ a₁, A₂.step q₂ a₂)
  start := (A₁.start, A₂.start)
  accept := { p | p.1 ∈ A₁.accept ∧ p.2 ∈ A₂.accept }
