import AFTD.Prelude

/-!
# restricted_base_ell_partition_count

Topic: elementary_number_theory   Node: 802ad8c31bc8

Provenance: formalization of a published result. Source: arXiv:2611.08109: The Calkin--Wilf problems on ell-ary partition functions, Section 1

The number of partitions of a natural number n into powers of ell with each power appearing at most k times, defined as the number of finitely supported functions a : Nat -> Nat bounded by k such that sum_m a(m) * ell^m = n.
-/

/-- The number of partitions of n into powers of ℓ with each power appearing at most k times. -/
noncomputable def restricted_base_ell_partition_count (k ℓ n : ℕ) : ℕ := Set.ncard {a : ℕ →₀ ℕ | (∀ m, a m ≤ k) ∧ a.sum (fun m c => c * ℓ ^ m) = n}
