import AFTD.Prelude

/-!
# twisted_frobenius_map

Topic: combinatorics   Node: 2c8ffc6994a6

Provenance: formalization of a published result. Source: scout/2611-17378-a-19-5-lower-bound-for-the-four-dimensional-erd-h-o-s-box-p.md:118

The twisted Frobenius map $Q(x) = x^{q^2+q}$ on a field $K$ for a positive integer $q$.
-/

/-- The twisted Frobenius map Q(x) = x^(q^2+q) on a field K with parameter q. -/
def twisted_frobenius_map (q : ℕ) {K : Type*} [Field K] (x : K) : K := x ^ (q ^ 2 + q)
