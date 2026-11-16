import AFTD.Prelude
import AFTD.Kb.Tcs.Op1370NeighborSignedSum

/-!
# op1370_neighbor_signed_nonleaf_nonzero

Topic: combinatorics   Node: 4dc86cbb807c

Provenance: helper lemma.

The signed odd-rank response sum is nonzero for nonzero point sign and neighborhood size not one.
-/

open Finset Matrix Polynomial
open scoped BigOperators

theorem op1370_neighbor_signed_nonleaf_nonzero
    {ι : Type*} [Fintype ι] [DecidableEq ι] (N : Finset ι) (x : ι)
    (hx : x ∉ N) (hcard : N.card ≠ 1) (σ : ι → ℚ) (hσ : σ x ≠ 0)
    (hs : ∀ a ∈ N, σ a = -σ x) :
    (∑ a, (if a = x then σ a else if a ∈ N then σ a else 0)) ≠ 0 := by
  have hs' : ∀ a ∈ N, σ a = (-1 : ℚ) * σ x := by simpa using hs
  rw [op1370_neighbor_signed_sum N x hx σ (-1) hs']
  have hcast : (N.card : ℚ) ≠ 1 := by
    intro h
    apply hcard
    exact Nat.cast_injective (by simpa using h : (N.card : ℚ) = ((1 : ℕ) : ℚ))
  have hbase : (1 : ℚ) - (N.card : ℚ) ≠ 0 := sub_ne_zero.mpr hcast.symm
  have he : σ x + (N.card : ℚ) * ((-1 : ℚ) * σ x) =
      (1 - (N.card : ℚ)) * σ x := by
    rw [sub_mul]
    simp [sub_eq_add_neg]
  rw [he]
  exact mul_ne_zero hbase hσ
