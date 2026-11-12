import AFTD.Prelude
import AFTD.Kb.Tcs.V

/-!
# rank_two_qutrit_projection_isometry

Topic: quantum   Node: 17f841d19e23

Provenance: helper lemma. Local compatibility helper for OP-693.

A rank-two orthogonal qutrit projection is the product of a two-column isometry and its adjoint.
-/

open Matrix
open scoped BigOperators Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSimpArgs false
private lemma in767_projectionproof_projection_eigenvalues (P : Matrix (Fin 3) (Fin 3) ℂ)
    (hP : P.IsHermitian) (hPP : P*P=P) (k : Fin 3) :
    hP.eigenvalues k = 0 ∨ hP.eigenvalues k = 1 := by
  let v : Fin 3 → ℂ := ⇑(hP.eigenvectorBasis k)
  have hv : v ≠ 0 := by
    intro h
    apply hP.eigenvectorBasis.orthonormal.ne_zero k
    apply WithLp.ofLp_injective 2
    exact h
  have he : P *ᵥ v = (hP.eigenvalues k : ℂ) • v := by
    simpa [RCLike.real_smul_eq_coe_smul] using hP.mulVec_eigenvectorBasis k
  have hh : (hP.eigenvalues k : ℂ) • ((hP.eigenvalues k : ℂ) • v) =
      (hP.eigenvalues k : ℂ) • v := by
    calc
      _ = P *ᵥ (P *ᵥ v) := by rw [he, Matrix.mulVec_smul, he]
      _ = (P*P) *ᵥ v := Matrix.mulVec_mulVec v P P
      _ = P *ᵥ v := by rw [hPP]
      _ = _ := he
  obtain ⟨i,hi⟩ := Function.ne_iff.mp hv
  have hi' : v i ≠ 0 := by simpa using hi
  have hcoord := congrFun hh i
  simp only [Pi.smul_apply, smul_eq_mul] at hcoord
  have hz : ((hP.eigenvalues k : ℂ)^2 - (hP.eigenvalues k : ℂ)) * v i = 0 := by
    linear_combination hcoord
  have heval : (hP.eigenvalues k : ℝ)^2 - hP.eigenvalues k = 0 := by
    have h := (mul_eq_zero.mp hz).resolve_right hi'
    exact_mod_cast h
  have hfactor : hP.eigenvalues k * (hP.eigenvalues k - 1)=0 := by nlinarith [heval]
  rcases mul_eq_zero.mp hfactor with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

private lemma in767_projectionproof_projection_rank_two_isometry
    (P : Matrix (Fin 3) (Fin 3) ℂ) (hP : P.IsHermitian) (hPP : P*P=P) (hRank : P.rank=2) :
    ∃ U : Matrix (Fin 3) (Fin 2) ℂ, Uᴴ*U=1 ∧ U*Uᴴ=P := by
  classical
  let I := {k : Fin 3 // hP.eigenvalues k ≠ 0}
  have hcard : Fintype.card I = 2 := by
    change Fintype.card {k : Fin 3 // hP.eigenvalues k ≠ 0} = 2
    rw [← hP.rank_eq_card_non_zero_eigs]
    exact hRank
  let e : Fin 2 ≃ I := Fintype.equivOfCardEq (by simp [hcard])
  let V : Matrix (Fin 3) (Fin 3) ℂ := hP.eigenvectorUnitary
  let U : Matrix (Fin 3) (Fin 2) ℂ := fun i j => V i (e j).val
  have hV : Vᴴ*V=1 := by
    have hh := Unitary.coe_star_mul_self hP.eigenvectorUnitary
    simpa [V, Matrix.star_eq_conjTranspose] using hh
  have hU : Uᴴ*U=1 := by
    ext i j
    have hh := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M (e i).val (e j).val) hV
    have heq : (e i).val = (e j).val ↔ i=j := by
      constructor
      · intro h
        exact e.injective (Subtype.ext h)
      · rintro rfl
        rfl
    simpa [U, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply, heq] using hh
  have hspec : P = V * Matrix.diagonal (fun k => (hP.eigenvalues k : ℂ)) * Vᴴ := by
    have hh := hP.spectral_theorem
    simpa [V, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose, Function.comp_def] using hh
  have heig (k : Fin 3) : hP.eigenvalues k = 0 ∨ hP.eigenvalues k = 1 :=
    in767_projectionproof_projection_eigenvalues P hP hPP k
  have hterm (i j k : Fin 3) :
      V i k * (hP.eigenvalues k : ℂ) * star (V j k) =
      if hP.eigenvalues k ≠ 0 then V i k * star (V j k) else 0 := by
    rcases heig k with h | h <;> simp [h]
  have hsub (i j : Fin 3) :
      (∑ k : Fin 3, if hP.eigenvalues k ≠ 0 then V i k * star (V j k) else 0) =
      ∑ k : I, V i k.val * star (V j k.val) := by
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype (Finset.univ.filter fun k : Fin 3 => hP.eigenvalues k ≠ 0) (by simp) _
  have hUU : U*Uᴴ=P := by
    ext i j
    have hh := congrArg (fun M : Matrix (Fin 3) (Fin 3) ℂ => M i j) hspec
    rw [Matrix.mul_apply] at hh
    simp only [Matrix.mul_diagonal, Matrix.conjTranspose_apply] at hh
    simp_rw [hterm] at hh
    rw [hsub] at hh
    have he := e.sum_comp (fun k : I => V i k.val * star (V j k.val))
    change (∑ k : Fin 2, V i (e k).val * star (V j (e k).val)) = P i j
    rw [he]
    exact hh.symm
  exact ⟨U,hU,hUU⟩

theorem rank_two_qutrit_projection_isometry :
  ∀ P : Matrix (Fin 3) (Fin 3) ℂ, P.IsHermitian → P*P = P → P.rank = 2 →
    ∃ U : Matrix (Fin 3) (Fin 2) ℂ, Uᴴ*U = 1 ∧ U*Uᴴ = P := by
  intro P hP hPP hRank
  exact in767_projectionproof_projection_rank_two_isometry P hP hPP hRank
