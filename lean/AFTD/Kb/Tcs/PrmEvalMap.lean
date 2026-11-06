import AFTD.Prelude

/-!
# prmEvalMap

Topic: information   Node: 98cb342dbb10

Provenance: formalization of a published result. Source: arXiv:2611.08203 Section 2.1

Given a field K and natural numbers d and m, prmEvalMap K d m is the K-linear evaluation map from degree-d homogeneous polynomials in m + 1 variables over K (MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K d) to functions from Projectivization K (Fin (m + 1) → K) to K, sending each homogeneous polynomial F to the function evaluating F at P.rep for each projective point P.
-/

/-- Evaluation map from degree-d homogeneous polynomials in m+1 variables to functions on ℙ^m(K). -/
noncomputable def prmEvalMap (K : Type*) [Field K] (d m : ℕ) :
    MvPolynomial.homogeneousSubmodule (Fin (m + 1)) K d →ₗ[K] (Projectivization K (Fin (m + 1) → K) → K) where
  toFun F := fun P => MvPolynomial.eval P.rep F.1
  map_add' F G := by
    ext P
    simp only [Submodule.coe_add, map_add, Pi.add_apply]
  map_smul' c F := by
    ext P
    simp only [Submodule.coe_smul, RingHom.id_apply, Pi.smul_apply, smul_eq_mul]
    rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C]
