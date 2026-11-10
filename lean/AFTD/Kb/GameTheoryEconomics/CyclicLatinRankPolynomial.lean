import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CyclicLatinMarket
import AFTD.Kb.GameTheoryEconomics.CyclicLatinRankSum
import AFTD.Kb.GameTheoryEconomics.IsStableMatching

/-!
# cyclic_latin_rank_polynomial

Topic: matching_markets   Node: 6b2c1766a88e

Provenance: formalization of a published result. Source: OP-1351

Given an order n with [NeZero n] and a bijection a : Fin n ≃ ZMod n, cyclic_latin_rank_polynomial n a is the polynomial in ℤ[X] defined by the sum over all matching permutations π : Equiv.Perm (ZMod n) of (if is_stable_matching (cyclic_latin_market n a) π then (Polynomial.X : Polynomial ℤ) ^ (cyclic_latin_rank_sum n a π) else 0).
-/

/-- Stable-matching proposer rank polynomial F_a(z) of cyclic Latin market a. -/
noncomputable def cyclic_latin_rank_polynomial (n : ℕ) [NeZero n]
    (a : Fin n ≃ ZMod n) : Polynomial ℤ :=
  open scoped Classical BigOperators in
  ∑ π : Equiv.Perm (ZMod n),
    if is_stable_matching (cyclic_latin_market n a) π
    then (Polynomial.X : Polynomial ℤ) ^ (cyclic_latin_rank_sum n a π)
    else 0
