import AFTD.Prelude

/-!
# perm_signed_order_sum

Topic: combinatorics   Node: d8506261b9bd

Provenance: formalization of a published result. Source: arXiv:2611.29409 line 144

The signed element order sum D_n = ∑_{σ ∈ S_n} sgn(σ) o(σ) over the symmetric group S_n of degree n, defined as `perm_signed_order_sum n`.
-/

/-- Signed sum of permutation orders in the symmetric group of degree n. -/
noncomputable def perm_signed_order_sum (n : ℕ) : ℤ := ∑ σ : Equiv.Perm (Fin n), (Equiv.Perm.sign σ : ℤ) * (orderOf σ : ℤ)
