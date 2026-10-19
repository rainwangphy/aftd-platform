import AFTD.Prelude

/-!
# TwoCounterInstr

Topic: automata   Node: 723d8821179f

Provenance: formalization of a published result. Source: arXiv:2610.23495, Section 2

An instruction of a 2-counter machine is either an update by a vector of integers (w₁, w₂), or a zero-test on the first counter or the second counter.
-/

/-- Instructions for a 2-counter machine: vector update or zero-test on either counter. -/
inductive TwoCounterInstr where | update (w₁ w₂ : ℤ) : TwoCounterInstr
  | zeroTest₁ : TwoCounterInstr
  | zeroTest₂ : TwoCounterInstr
  deriving DecidableEq
