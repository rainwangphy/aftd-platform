import AFTD.Prelude

/-!
# trace_walsh_coeff

Topic: cryptography   Node: 3edcb7a6a4a1

Provenance: formalization of a published result. Source: arXiv:2611.10269 Sec. 2

The Walsh transform coefficient of a Boolean function f : E → ZMod 2 on a finite field E at frequency α with respect to the absolute trace form, given by the sum over x in E of (-1)^(f(x) + Tr(α x)).
-/

/-- The Walsh transform coefficient of a Boolean function on a finite field E at frequency α with respect to the trace form. -/
noncomputable def trace_walsh_coeff (E : Type*) [Field E] [Fintype E] [Algebra (ZMod 2) E] (f : E → ZMod 2) (α : E) : ℤ := ∑ x : E, if f x + Algebra.trace (ZMod 2) E (α * x) = 0 then (1 : ℤ) else -1
