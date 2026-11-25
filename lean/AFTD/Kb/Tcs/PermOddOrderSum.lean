import AFTD.Prelude

/-!
# perm_odd_order_sum

Topic: combinatorics   Node: a87b138dcefd

Provenance: formalization of a published result. Source: arXiv:2611.29409 line 156

The sum V_n of orders of odd-order permutations in the symmetric group S_n of degree n, valued in the integers ℤ: ∑_{σ ∈ S_n, o(σ) odd} (o(σ) : ℤ), defined as `perm_odd_order_sum (n : ℕ) : ℤ`.
-/

/-- Sum of orders of odd-order permutations in the symmetric group of degree n, valued in ℤ. -/
noncomputable def perm_odd_order_sum (n : ℕ) : ℤ := ∑ σ ∈ Finset.filter (fun σ : Equiv.Perm (Fin n) => Odd (orderOf σ)) Finset.univ, (orderOf σ : ℤ)
