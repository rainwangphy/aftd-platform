import AFTD.Prelude

/-!
# LownerHeinzCore.schur_conj_eq_diagonal

Topic: quantum   Node: b5e6508c4c4a

Provenance: formalization of a published result. Source: QuantumInfo, `LownerHeinzCore.schur_conj_eq_diagonal`. Lean proof by Kei Tsukamoto, Kento Mori, Hayata Yamasaki, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/LownerHeinzCore.lean (Copyright (c) 2026 Hayata Yamasaki. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LownerHeinzCore.schur_conj_eq_diagonal
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
universe u v in
open CFC in
variable {𝓐 : Type u} in
variable [CStarAlgebra 𝓐] [PartialOrder 𝓐] [StarOrderedRing 𝓐] in
variable [Nontrivial 𝓐] in
variable [NonnegSpectrumClass ℝ 𝓐] in
omit [Nontrivial (𝓐)] in
omit [PartialOrder 𝓐] [StarOrderedRing 𝓐] [NonnegSpectrumClass ℝ 𝓐] in
lemma LownerHeinzCore.schur_conj_eq_diagonal {C D invC : 𝓐} (hInvC_sa : IsSelfAdjoint invC)
    (invC_mul_C : invC * C = (1 : 𝓐)) (C_mul_invC : C * invC = (1 : 𝓐)) :
    star (!![(1 : 𝓐), -invC; 0, 1] : Matrix (Fin 2) (Fin 2) (𝓐))
        * (!![C, 1; 1, D] : Matrix (Fin 2) (Fin 2) (𝓐))
        * (!![(1 : 𝓐), -invC; 0, 1] : Matrix (Fin 2) (Fin 2) (𝓐))
      = Matrix.diagonal (fun i : Fin 2 => if i = 0 then C else D - invC) := by
  set U : Matrix (Fin 2) (Fin 2) (𝓐) := !![(1 : 𝓐), -invC; 0, 1]
  have hstarU : star U = !![(1 : 𝓐), 0; -invC, 1] := by
    dsimp [U]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hInvC_sa.star_eq]
  have hP :
      star U * (!![C, 1; 1, D] : Matrix (Fin 2) (Fin 2) (𝓐)) =
        !![C, 1; -invC * C + 1, -invC + D] := by
    simp [hstarU, U]
  have hQ :
      star U * (!![C, 1; 1, D] : Matrix (Fin 2) (Fin 2) (𝓐)) * U =
        !![C, 0; 0, D - invC] := by
    have hstep :
        star U * (!![C, 1; 1, D] : Matrix (Fin 2) (Fin 2) (𝓐)) * U =
          (!![C, 1; -invC * C + 1, -invC + D] : Matrix (Fin 2) (Fin 2) (𝓐)) * U := by
      simpa [mul_assoc] using congrArg (fun X => X * U) hP
    dsimp [U] at hstep ⊢
    simp [hstep, C_mul_invC, invC_mul_C, sub_eq_add_neg, add_comm]
  have hdiag :
      (Matrix.diagonal (fun i : Fin 2 => if i = 0 then C else D - invC)) =
        (!![C, 0; 0, D - invC] : Matrix (Fin 2) (Fin 2) (𝓐)) := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal]
  simpa [hdiag] using hQ
