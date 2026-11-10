import AFTD.Prelude

/-!
# cyclic_latin_rank_sum

Topic: matching_markets   Node: 4ff28588db00

Provenance: formalization of a published result. Source: OP-1351

Given an order n with [NeZero n], a bijection a : Fin n ≃ ZMod n, and a matching permutation π : Equiv.Perm (ZMod n), the aggregate proposer rank cyclic_latin_rank_sum n a π is the sum over all men i : ZMod n of the rank (a.symm (i + π i) : ℕ).
-/

open scoped BigOperators in
/-- Aggregate proposer rank of a matching under cyclic Latin ordering a. -/
def cyclic_latin_rank_sum (n : ℕ) [NeZero n] (a : Fin n ≃ ZMod n)
    (π : Equiv.Perm (ZMod n)) : ℕ := ∑ i : ZMod n, (a.symm (i + π i) : ℕ)
