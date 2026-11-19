import AFTD.Prelude
import AFTD.Kb.Tcs.CrossRatioEvaluationSet

/-!
# zero_mem_cross_ratio_evaluation_set

Topic: information   Node: 2bf3b90abe57

Provenance: helper lemma. arXiv:2611.21275 Definition 23

For any field F, finite subfield K of F, and element θ in F, 0 belongs to cross_ratio_evaluation_set K θ.
-/

/-- Zero is an element of cross_ratio_evaluation_set K θ. -/
theorem zero_mem_cross_ratio_evaluation_set {F : Type*} [Field F] [DecidableEq F]
    (K : Subfield F) [Fintype K] (θ : F) :
    0 ∈ cross_ratio_evaluation_set K θ :=
  Finset.mem_insert_self 0 _
