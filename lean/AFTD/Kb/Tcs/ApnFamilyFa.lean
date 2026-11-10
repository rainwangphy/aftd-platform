import AFTD.Prelude

/-!
# apn_family_fa

Topic: cryptography   Node: 50df9fdbcf90

Provenance: formalization of a published result. Source: arXiv:2611.10269 Sec. 7

For an element a in a finite field E of characteristic 2, the function F_a(x) is defined by x^3 + a⁻¹ * Tr(a^3 * x^9).
-/

/-- The quadratic map F_a(x) = x^3 + a⁻¹ Tr(a^3 x^9) on a finite field E of characteristic 2. -/
noncomputable def apn_family_fa (E : Type*) [Field E] [Fintype E] [Algebra (ZMod 2) E] (a : E) (x : E) : E := x ^ 3 + a⁻¹ * algebraMap (ZMod 2) E (Algebra.trace (ZMod 2) E (a ^ 3 * x ^ 9))
