import AFTD.Prelude
import AFTD.Kb.Physics.ThermomajorizationPointwiseMissedError
import AFTD.Kb.Physics.ThermomajorizationMissedError
import AFTD.Kb.Physics.ThermomajorizationProbeGapError
import AFTD.Kb.Physics.ThermomajorizationPointwiseMissedErrorGeGapError
import AFTD.Kb.Physics.ThermomajorizationPointwiseMissedErrorLeGapError
import AFTD.Kb.Physics.ThermomajorizationMissedErrorEqISupPointwise

/-!
# thermomajorization_sparse_probe_sharp_missed_trace_error

Topic: quantum_mechanics   Node: 9338a7c218d5

Provenance: formalization of a published result. Source: arXiv:2610.35433, Population capacity and the geometry of thermomajorization

For any dimension n ≥ 2 and probe set F ⊆ {1,...,n-1}, the worst-case thermomajorization prefix error missed by F at an unprobed rank j ∈ {1,...,n-1} \ F equals thermomajorization_probe_gap_error a b j where a = max({0} ∪ {k ∈ F : k < j}) and b = min({n} ∪ {k ∈ F : k > j}), and for any probe set with nonempty unprobed set {1,...,n-1} \ F, the global conversion missed error thermomajorization_missed_error n F equals the supremum of thermomajorization_probe_gap_error a b j over all unprobed j.
-/

/-- Sharp missed trace error for sparse binary probes under thermomajorization at uniform Gibbs weights (OP-1727). -/
theorem thermomajorization_sparse_probe_sharp_missed_trace_error :
    (∀ (n : ℕ) (hn : 2 ≤ n) (F : Finset ℕ) (hF : F ⊆ Finset.Ioo 0 n)
      (j : ℕ) (hj : j ∈ Finset.Ioo 0 n \ F),
      let a := (insert 0 (F.filter (· < j))).max' (Finset.insert_nonempty 0 _)
      let b := (insert n (F.filter (j < ·))).min' (Finset.insert_nonempty n _)
      thermomajorization_pointwise_missed_error n F j =
        thermomajorization_probe_gap_error a b j) ∧
    (∀ (n : ℕ) (hn : 2 ≤ n) (F : Finset ℕ) (hF : F ⊆ Finset.Ioo 0 n)
      (hF_ne : (Finset.Ioo 0 n \ F).Nonempty),
      thermomajorization_missed_error n F =
        ⨆ j ∈ Finset.Ioo 0 n \ F,
          let a := (insert 0 (F.filter (· < j))).max' (Finset.insert_nonempty 0 _)
          let b := (insert n (F.filter (j < ·))).min' (Finset.insert_nonempty n _)
          thermomajorization_probe_gap_error a b j) := by
  constructor
  · intro n hn F hF j hj
    exact le_antisymm
      (thermomajorization_pointwise_missed_error_le_gap_error n hn F hF j hj)
      (thermomajorization_pointwise_missed_error_ge_gap_error n hn F hF j hj)
  · intro n hn F hF hF_ne
    rw [thermomajorization_missed_error_eq_iSup_pointwise n hn F hF hF_ne]
    congr 1 with j
    congr 1 with hj
    exact le_antisymm
      (thermomajorization_pointwise_missed_error_le_gap_error n hn F hF j hj)
      (thermomajorization_pointwise_missed_error_ge_gap_error n hn F hF j hj)
