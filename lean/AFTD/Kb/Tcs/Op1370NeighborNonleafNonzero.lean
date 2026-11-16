import AFTD.Prelude
import AFTD.Kb.Tcs.Op1370NeighborConstantSum

/-!
# op1370_neighbor_nonleaf_nonzero

Topic: combinatorics   Node: 8d05633888cd

Provenance: helper lemma.

The odd-rank response sum is nonzero whenever the neighborhood size is not one.
-/

open Finset Matrix Polynomial
open scoped BigOperators

theorem op1370_neighbor_nonleaf_nonzero
    {ι : Type*} [Fintype ι] [DecidableEq ι] (N : Finset ι) (x : ι)
    (hx : x ∉ N) (hcard : N.card ≠ 1) :
    (∑ a, (if a = x then 1 else if a ∈ N then (-1 : ℚ) else 0)) ≠ 0 := by
  rw [op1370_neighbor_constant_sum N x hx (-1)]
  have hcast : (N.card : ℚ) ≠ 1 := by
    intro h
    apply hcard
    exact Nat.cast_injective (by simpa using h : (N.card : ℚ) = ((1 : ℕ) : ℚ))
  simpa [sub_eq_add_neg] using (sub_ne_zero.mpr hcast.symm : (1 : ℚ) - (N.card : ℚ) ≠ 0)
