import AFTD.Prelude
import AFTD.Kb.Tcs.ZeroSumRamseyProperty

/-!
# zero_sum_ramsey_number

Topic: combinatorics   Node: d27cc400dd7d

Provenance: formalization of a published result. Source: arXiv:2611.14160 Section 1

The zero-sum Ramsey number R(H, Z_m) of a simple graph H over Z_m is the infimum of the natural numbers N such that every ZMod m edge labeling of K_N contains a copy of H with edge sum zero.
-/

/-- The zero-sum Ramsey number R(H, Z_m) of a simple graph H over Z_m. -/
noncomputable def zero_sum_ramsey_number {V : Type*} [Fintype V]
    (H : SimpleGraph V) [Fintype H.edgeSet] (m : ℕ) : ℕ :=
  sInf {N : ℕ | zero_sum_ramsey_property H m N}
