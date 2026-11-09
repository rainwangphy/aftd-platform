import AFTD.Prelude
import AFTD.Kb.Tcs.IsTwoStronglyEuclidean
import AFTD.Kb.Tcs.IsOneStronglyEuclidean

/-!
# is_one_strongly_euclidean_of_two_strongly_euclidean

Topic: algorithms   Node: a8cf9ecf993f

Provenance: helper lemma. arXiv:2611.08546 "Bourgain's Theorem for a Union of Euclidean Metric Spaces", Section 1.1

Let X be a metric space and V a subset of X. If V is 2-strongly Euclidean in X, then V is 1-strongly Euclidean in X.
-/

/-- Every 2-strongly Euclidean subset of a metric space is 1-strongly Euclidean. -/
lemma is_one_strongly_euclidean_of_two_strongly_euclidean.{u} {X : Type u} [MetricSpace X]
    {V : Set X} (h : IsTwoStronglyEuclidean V) :
    IsOneStronglyEuclidean V := by
  intro x
  obtain ⟨H, nH, iH, cH, f, hf⟩ := h x x
  have h_eq : (V ∪ {x, x} : Set X) = V ∪ {x} := by simp
  refine ⟨H, nH, iH, cH, ?_⟩
  rw [← h_eq]
  exact ⟨f, hf⟩
