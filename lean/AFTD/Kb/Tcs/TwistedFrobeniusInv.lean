import AFTD.Prelude
import AFTD.Kb.Tcs.TwistedFrobeniusMap

/-!
# twisted_frobenius_inv

Topic: combinatorics   Node: 3ed088e769e0

Provenance: formalization of a published result. Source: scout/2611-17378-a-19-5-lower-bound-for-the-four-dimensional-erd-h-o-s-box-p.md:143

The inverse $Q^{-1}$ of the twisted Frobenius map $Q(x) = x^{q^2+q}$.
-/

/-- The inverse of the twisted Frobenius map Q(x) = x^(q^2+q). -/
noncomputable def twisted_frobenius_inv (q : ℕ) {K : Type*} [Field K] (y : K) : K := Function.invFun (twisted_frobenius_map q) y
