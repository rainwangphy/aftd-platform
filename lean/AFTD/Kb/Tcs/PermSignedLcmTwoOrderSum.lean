import AFTD.Prelude

/-!
# perm_signed_lcm_two_order_sum

Topic: combinatorics   Node: 63abece9d82c

Provenance: formalization of a published result. Source: arXiv:2611.29409 line 346

The signed lcm order sum D_n^* = ∑_{σ ∈ S_n} sgn(σ) lcm(2, o(σ)) over the symmetric group S_n of degree n, defined as `perm_signed_lcm_two_order_sum n`.
-/

/-- Signed sum of lcm(2, order) of permutations in the symmetric group of degree n. -/
noncomputable def perm_signed_lcm_two_order_sum (n : ℕ) : ℤ := ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℤ) * (Nat.lcm 2 (orderOf σ) : ℤ)
