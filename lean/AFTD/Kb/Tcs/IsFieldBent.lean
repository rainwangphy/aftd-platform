import AFTD.Prelude
import AFTD.Kb.Tcs.TraceWalshCoeff

/-!
# is_field_bent

Topic: cryptography   Node: 754e724259c7

Provenance: formalization of a published result. Source: arXiv:2611.10269 Sec. 2

A Boolean function f : E → ZMod 2 on a finite field E of dimension 2m over F_2 is bent if its Walsh transform coefficient at every frequency α in E has absolute value 2^m.
-/

/-- A Boolean function on a finite field of dimension 2m over F_2 is bent if all its Walsh transform coefficients have absolute value 2^m. -/
def is_field_bent (E : Type*) [Field E] [Fintype E] [Algebra (ZMod 2) E] (m : ℕ) (f : E → ZMod 2) : Prop := ∀ α : E, |trace_walsh_coeff E f α| = (2 : ℤ) ^ m
