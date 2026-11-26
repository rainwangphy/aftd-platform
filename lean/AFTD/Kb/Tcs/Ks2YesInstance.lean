import AFTD.Prelude
import AFTD.Kb.Tcs.Ks2InstanceVector
import AFTD.Kb.Tcs.Ks2InstanceOuter

/-!
# ks2_yes_instance

Topic: np_completeness   Node: 28566cc1c0eb

Provenance: formalization of a published result. Source: arXiv:2611.27740, Problem 1.1: the promise (norms at most alpha, outer products summing to the identity) together with the property to decide (a signing with operator norm at most c sqrt(alpha)). A signing is a list of signs, one per position of the indexed family.

With explicit arguments c : ℝ, α : ℚ, d : ℕ and vs : List (ℚ × List (ℚ × ℚ)), in this order, the proposition that (α, vs) is a valid input of the algorithmic Kadison-Singer problem in dimension d with a signing of discrepancy at most c sqrt(α); it is the conjunction of four conditions: (1) 0 < α; (2) for every entry p of vs, the squared Euclidean norm ∑_j ‖(ks2_instance_vector d p) j‖² (sum over j : Fin d) is at most α (cast to ℝ); (3) the sum of the list of matrices ks2_instance_outer d p, for p in vs (List.map then List.sum), equals the identity matrix 1; (4) there exists a list s of Booleans with s.length = vs.length such that the operator norm of Matrix.toEuclideanCLM (with n := Fin d, 𝕜 := ℂ) applied to the signed sum, namely the List.sum of List.zipWith (fun b p => ε(b) • ks2_instance_outer d p) s vs with ε(b) = 1 in ℂ if b is true and −1 if b is false, is at most c * Real.sqrt α (α cast to ℝ). The norm is the operator norm of continuous linear maps on EuclideanSpace ℂ (Fin d), i.e. the spectral norm of the matrix.
-/

/-- A valid Kadison-Singer input `(α, vs)` in dimension `d` having a signing of spectral norm at most `c √α`. -/
def ks2_yes_instance (c : ℝ) (α : ℚ) (d : ℕ) (vs : List (ℚ × List (ℚ × ℚ))) : Prop :=
  0 < α ∧ (∀ p ∈ vs, ∑ j, ‖ks2_instance_vector d p j‖ ^ 2 ≤ (α : ℝ)) ∧
  (vs.map (ks2_instance_outer d)).sum = 1 ∧
  ∃ s : List Bool, s.length = vs.length ∧
    ‖Matrix.toEuclideanCLM (n := Fin d) (𝕜 := ℂ)
      ((List.zipWith (fun b p => (if b then (1 : ℂ) else -1) • ks2_instance_outer d p) s vs).sum)‖
      ≤ c * Real.sqrt (α : ℝ)
