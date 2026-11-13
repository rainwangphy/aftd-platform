import AFTD.Prelude

/-!
# cycle_power_dyadic_sparse_defect_support

Topic: combinatorics   Node: c9c400d5afc4

Provenance: helper lemma. RT-1 and OP-205, arXiv:2610.15635. The sparse constant family was identified in experiment 22695; it is a weakened-coverage obstruction, not a full graph-cover model.

For exponent t, the sparse constant defect support consists of 0, 2^(t−2)−1, and 2^t−2^j for all j<t−2.
-/

def cycle_power_dyadic_sparse_defect_support (t : ℕ) : Finset ℕ := let q := 2^(t-2)
    ({0, q-1} : Finset ℕ) ∪ (Finset.range (t-2)).image (fun j => 2^t - 2^j)
