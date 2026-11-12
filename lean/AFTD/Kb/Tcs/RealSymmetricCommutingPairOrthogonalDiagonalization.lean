import AFTD.Prelude
import AFTD.Kb.Physics.IsSymmetric
import AFTD.Kb.Tcs.V

/-!
# real_symmetric_commuting_pair_orthogonal_diagonalization

Topic: quantum   Node: 0daf0dc0b3f3

Provenance: helper lemma. Linear-algebra helper for the rank-four source in OP-693.

Commuting real symmetric square matrices have a common real orthogonal eigenbasis.
-/

open Matrix
open scoped BigOperators Matrix
set_option backward.isDefEq.respectTransparency false

private lemma in767_diagonalproof_real_commuting_diagonal (n : ℕ) (R S : Matrix (Fin n) (Fin n) ℝ)
    (hR : R.transpose=R) (hS : S.transpose=S) (hRS : R*S=S*R) :
    ∃ (O : Matrix (Fin n) (Fin n) ℝ) (r s : Fin n → ℝ),
      O.transpose * O = 1 ∧ O * O.transpose = 1 ∧
      R = O * Matrix.diagonal r * O.transpose ∧
      S = O * Matrix.diagonal s * O.transpose := by
  classical
  let A := R.toEuclideanLin
  let B := S.toEuclideanLin
  have hA : A.IsSymmetric := by
    apply Matrix.isSymmetric_toEuclideanLin_iff.mpr
    simpa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hR
  have hB : B.IsSymmetric := by
    apply Matrix.isSymmetric_toEuclideanLin_iff.mpr
    simpa [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using hS
  have hAB : Commute A B := by
    apply LinearMap.ext
    intro x
    apply WithLp.ofLp_injective 2
    simp only [Module.End.mul_apply, A, B, Matrix.ofLp_toEuclideanLin_apply]
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hRS]
  let V : ℝ × ℝ → Submodule ℝ (EuclideanSpace ℝ (Fin n)) := fun i =>
    Module.End.eigenspace A i.2 ⊓ Module.End.eigenspace B i.1
  have hV : DirectSum.IsInternal V := hA.directSum_isInternal_of_commute hB hAB
  have hVo : OrthogonalFamily ℝ (fun i => V i) (fun i => (V i).subtypeₗᵢ) :=
    hA.orthogonalFamily_eigenspace_inf_eigenspace hB
  let vf : ∀ i : ℝ × ℝ, Module.Basis (Fin (Module.finrank ℝ (V i))) ℝ (V i) :=
    fun i => (stdOrthonormalBasis ℝ (V i)).toBasis
  let C := hV.collectedBasis vf
  have hCo : Orthonormal ℝ C := DirectSum.IsInternal.collectedBasis_orthonormal hVo hV
    (fun i => (stdOrthonormalBasis ℝ (V i)).orthonormal)
  letI : Finite (Σ i : ℝ × ℝ, Fin (Module.finrank ℝ (V i))) :=
    Module.Finite.finite_basis C
  letI : Fintype (Σ i : ℝ × ℝ, Fin (Module.finrank ℝ (V i))) := Fintype.ofFinite _
  let D := C.toOrthonormalBasis hCo
  let e := C.indexEquiv (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  let E := D.reindex e
  let r : Fin n → ℝ := fun j => ((e.symm j).1).2
  let s : Fin n → ℝ := fun j => ((e.symm j).1).1
  have heig (j : Fin n) : A (E j) = r j • E j ∧ B (E j) = s j • E j := by
    have hh := hV.collectedBasis_mem vf (e.symm j)
    have hh' : E j ∈ V (e.symm j).1 := by
      simpa [E, D, C, OrthonormalBasis.coe_reindex] using hh
    exact ⟨Module.End.mem_eigenspace_iff.mp hh'.1, Module.End.mem_eigenspace_iff.mp hh'.2⟩
  let O : Matrix (Fin n) (Fin n) ℝ := fun i j => (E j).ofLp i
  have hO : O ∈ Matrix.orthogonalGroup (Fin n) ℝ := by
    have hh := (EuclideanSpace.basisFun (Fin n) ℝ).toMatrix_orthonormalBasis_mem_orthogonal E
    convert hh using 1
    ext i j
    simp [O, Module.Basis.toMatrix_apply, EuclideanSpace.basisFun_repr]
  have hOtO : O.transpose*O=1 := (Matrix.mem_orthogonalGroup_iff' _ _).mp hO
  have hOOt : O*O.transpose=1 := (Matrix.mem_orthogonalGroup_iff _ _).mp hO
  have hRO : R*O=O*Matrix.diagonal r := by
    ext i j
    rw [Matrix.mul_diagonal]
    have hh := congrArg (fun x : EuclideanSpace ℝ (Fin n) => x.ofLp i) (heig j).1
    simpa [A, O, Matrix.mul_apply, Matrix.ofLp_toEuclideanLin_apply, Matrix.mulVec, dotProduct, mul_comm] using hh
  have hSO : S*O=O*Matrix.diagonal s := by
    ext i j
    rw [Matrix.mul_diagonal]
    have hh := congrArg (fun x : EuclideanSpace ℝ (Fin n) => x.ofLp i) (heig j).2
    simpa [B, O, Matrix.mul_apply, Matrix.ofLp_toEuclideanLin_apply, Matrix.mulVec, dotProduct, mul_comm] using hh
  refine ⟨O,r,s,hOtO,hOOt,?_,?_⟩
  · calc
      R = R * (O*O.transpose) := by rw [hOOt, mul_one]
      _ = (R*O)*O.transpose := by rw [Matrix.mul_assoc]
      _ = (O*Matrix.diagonal r)*O.transpose := by rw [hRO]
  · calc
      S = S * (O*O.transpose) := by rw [hOOt, mul_one]
      _ = (S*O)*O.transpose := by rw [Matrix.mul_assoc]
      _ = (O*Matrix.diagonal s)*O.transpose := by rw [hSO]

theorem real_symmetric_commuting_pair_orthogonal_diagonalization :
  ∀ (n : ℕ) (R S : Matrix (Fin n) (Fin n) ℝ),
    R.transpose = R → S.transpose = S → R*S = S*R →
    ∃ (O : Matrix (Fin n) (Fin n) ℝ) (r s : Fin n → ℝ),
      O.transpose * O = 1 ∧ O * O.transpose = 1 ∧
      R = O * Matrix.diagonal r * O.transpose ∧
      S = O * Matrix.diagonal s * O.transpose := by
  exact in767_diagonalproof_real_commuting_diagonal
