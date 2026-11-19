import AFTD.Prelude

/-!
# cross_ratio_evaluation_set

Topic: information   Node: 2fb9c0493c84

Provenance: formalization of a published result. Source: arXiv:2611.21275 Definition 23

For a field F, a finite subfield K of F, and an element θ in F, cross_ratio_evaluation_set K θ is the finite subset of F consisting of 0 and the elements (t - θ)⁻¹ for all t in K.
-/

/-- The evaluation set X_θ = {(t - θ)⁻¹ : t ∈ K} ∪ {0} in F. -/
def cross_ratio_evaluation_set {F : Type*} [Field F] [DecidableEq F]
    (K : Subfield F) [Fintype K] (θ : F) : Finset F := insert 0 (Finset.univ.image (fun (t : K) => ((t : F) - θ)⁻¹))
