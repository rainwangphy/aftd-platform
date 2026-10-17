import AFTD.Prelude
import AFTD.Kb.Tcs.LownerHeinzCoreOperatorConvexOn
import AFTD.Kb.Tcs.LownerHeinzCoreCfcR
import AFTD.Kb.Tcs.LownerHeinzCoreOneDivOperatorConvexOnIoi
import AFTD.Kb.Physics.LinearPMapIsSelfAdjointSmul

/-!
# LownerHeinzCore.one_div_add_t_operatorConvexOn_Ici

Topic: quantum   Node: cbf6341ca780

Provenance: formalization of a published result. Source: QuantumInfo, `LownerHeinzCore.one_div_add_t_operatorConvexOn_Ici`. Lean proof by Kei Tsukamoto, Kento Mori, Hayata Yamasaki, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/HayataGroup/TraceInequality/LownerHeinzCore.lean (Copyright (c) 2026 Hayata Yamasaki. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

LownerHeinzCore.one_div_add_t_operatorConvexOn_Ici
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open LownerHeinzCore in
universe u v in
open CFC in
variable {𝓐 : Type u} in
variable [CStarAlgebra 𝓐] [PartialOrder 𝓐] [StarOrderedRing 𝓐] in
variable [Nontrivial 𝓐] in
variable [NonnegSpectrumClass ℝ 𝓐] in
theorem LownerHeinzCore.one_div_add_t_operatorConvexOn_Ici : ∀ (t : ℝ), 0 < t →
  OperatorConvexOn (𝓐 := 𝓐) (Set.Ici (0 : ℝ)) (fun x : ℝ ↦ 1 / (x + t)) := by
  /-
  It follows from one_div_operatorConvexOn_Ioi
  -/
  intro t ht
  dsimp [OperatorConvexOn]
  intro A B θ hA hB hθ0 hθ1 As Bs
  -- rewrite `1 / (x + t)` as `(x + t)⁻¹` for `simp`/`cfc` lemmas
  simp only [one_div]
  -- Reduce to operator convexity of `x ↦ x⁻¹` on `Ioi 0` by shifting by `t`.
  set C : 𝓐 := (1 - θ) • A + θ • B
  have hC : IsSelfAdjoint C := by
    simpa [C] using (IsSelfAdjoint.all (1 - θ)).smul hA |>.add ((IsSelfAdjoint.all θ).smul hB)
  set shift : ℝ → ℝ := fun x ↦ x + t
  set T : 𝓐 := algebraMap ℝ (𝓐) t
  have hT : IsSelfAdjoint T := by
    simpa [T] using (IsSelfAdjoint.algebraMap (A := 𝓐) (r := t)
      (hr := IsSelfAdjoint.all (t : ℝ)))
  have A_nonneg : 0 ≤ A := by
    have h0 : 0 ≤ cfcR (fun x : ℝ ↦ x) A := by
      dsimp [cfcR]
      apply cfc_nonneg
      intro x hx
      simpa [Set.Ici] using (As hx)
    simpa [cfcR, cfc_id' (R := ℝ) (a := A) (ha := hA)] using h0
  have B_nonneg : 0 ≤ B := by
    have h0 : 0 ≤ cfcR (fun x : ℝ ↦ x) B := by
      dsimp [cfcR]
      apply cfc_nonneg
      intro x hx
      simpa [Set.Ici] using (Bs hx)
    simpa [cfcR, cfc_id' (R := ℝ) (a := B) (ha := hB)] using h0
  have C_nonneg : 0 ≤ C := by
    simpa [C] using add_nonneg (smul_nonneg (sub_nonneg.mpr hθ1) A_nonneg) (smul_nonneg hθ0 B_nonneg)
  have hA_shift : cfcR shift A = A + T := by
    dsimp [cfcR, shift, T]
    simpa [cfc_id' (R := ℝ) (a := A) (ha := hA)] using
      (cfc_add_const (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (r := t)
        (f := fun x : ℝ ↦ x) (a := A) (ha := hA))
  have hB_shift : cfcR shift B = B + T := by
    dsimp [cfcR, shift, T]
    simpa [cfc_id' (R := ℝ) (a := B) (ha := hB)] using
      (cfc_add_const (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (r := t)
        (f := fun x : ℝ ↦ x) (a := B) (ha := hB))
  have hC_shift : cfcR shift C = C + T := by
    dsimp [cfcR, shift, T]
    simpa [cfc_id' (R := ℝ) (a := C) (ha := hC)] using
      (cfc_add_const (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (r := t)
        (f := fun x : ℝ ↦ x) (a := C) (ha := hC))
  set A1 : 𝓐 := A + T
  set B1 : 𝓐 := B + T
  set C1 : 𝓐 := (1 - θ) • A1 + θ • B1
  have hA1_sa : IsSelfAdjoint A1 := by
    subst A1
    exact hA.add hT
  have hB1_sa : IsSelfAdjoint B1 := by
    subst B1
    exact hB.add hT
  have specA1 : spectrum ℝ A1 ⊆ Set.Ioi (0 : ℝ) := by
    intro x hx
    have hs : spectrum ℝ (cfc shift A) = shift '' spectrum ℝ A := by
      simpa [shift] using
        (cfc_map_spectrum (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (a := A)
          (f := shift) (ha := hA))
    have hx' : x ∈ shift '' spectrum ℝ A := by
      have hx0 : x ∈ spectrum ℝ (cfc shift A) := by
        have hval : cfc shift A = A1 := by
          simpa [cfcR, shift, A1] using hA_shift
        simpa [hval] using hx
      simpa [hs] using hx0
    rcases hx' with ⟨y, hy, rfl⟩
    have hy0 : 0 ≤ y := by
      simpa [Set.Ici] using (As hy)
    simpa [Set.Ioi] using (add_pos_of_nonneg_of_pos hy0 ht)
  have specB1 : spectrum ℝ B1 ⊆ Set.Ioi (0 : ℝ) := by
    intro x hx
    have hs : spectrum ℝ (cfc shift B) = shift '' spectrum ℝ B := by
      simpa [shift] using
        (cfc_map_spectrum (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (a := B)
          (f := shift) (ha := hB))
    have hx' : x ∈ shift '' spectrum ℝ B := by
      have hx0 : x ∈ spectrum ℝ (cfc shift B) := by
        have hval : cfc shift B = B1 := by
          simpa [cfcR, shift, B1] using hB_shift
        simpa [hval] using hx
      simpa [hs] using hx0
    rcases hx' with ⟨y, hy, rfl⟩
    have hy0 : 0 ≤ y := by
      simpa [Set.Ici] using (Bs hy)
    simpa [Set.Ioi] using (add_pos_of_nonneg_of_pos hy0 ht)
  have hC1 : C1 = C + T := by
    subst A1 B1 C1
    simp [C, add_assoc, add_left_comm, add_comm, smul_add]
  have hshift_ne0_A : ∀ x ∈ spectrum ℝ A, shift x ≠ 0 := by
    intro x hx
    have hx0 : 0 ≤ x := by
      simpa [Set.Ici] using (As hx)
    exact ne_of_gt (by simpa [shift] using (add_pos_of_nonneg_of_pos hx0 ht))
  have hshift_ne0_B : ∀ x ∈ spectrum ℝ B, shift x ≠ 0 := by
    intro x hx
    have hx0 : 0 ≤ x := by
      simpa [Set.Ici] using (Bs hx)
    exact ne_of_gt (by simpa [shift] using (add_pos_of_nonneg_of_pos hx0 ht))
  have hshift_ne0_C : ∀ x ∈ spectrum ℝ C, shift x ≠ 0 :=
    fun x hx ↦ ne_of_gt (by simpa [shift] using (add_pos_of_nonneg_of_pos (spectrum_nonneg_of_nonneg C_nonneg hx) ht))
  have hA_inv : cfcR (fun x : ℝ ↦ (x + t)⁻¹) A = Ring.inverse A1 := by
    have h' : cfc (fun x : ℝ ↦ (shift x)⁻¹) A = Ring.inverse (cfc shift A) := by
      simpa [shift] using (cfc_inv (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint)
        (f := shift) (a := A) hshift_ne0_A (ha := hA))
    have hval : cfc shift A = A1 := by
      simpa [cfcR, shift, A1] using hA_shift
    simpa [cfcR, shift, hval] using h'
  have hB_inv : cfcR (fun x : ℝ ↦ (x + t)⁻¹) B = Ring.inverse B1 := by
    have h' : cfc (fun x : ℝ ↦ (shift x)⁻¹) B = Ring.inverse (cfc shift B) := by
      simpa [shift] using (cfc_inv (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint)
        (f := shift) (a := B) hshift_ne0_B (ha := hB))
    have hval : cfc shift B = B1 := by
      simpa [cfcR, shift, B1] using hB_shift
    simpa [cfcR, shift, hval] using h'
  have hC_inv : cfcR (fun x : ℝ ↦ (x + t)⁻¹) C = Ring.inverse (C + T) := by
    have h' : cfc (fun x : ℝ ↦ (shift x)⁻¹) C = Ring.inverse (cfc shift C) := by
      simpa [shift] using (cfc_inv (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint)
        (f := shift) (a := C) hshift_ne0_C (ha := hC))
    have hval : cfc shift C = C + T := by
      simpa [cfcR, shift] using hC_shift
    simpa [cfcR, shift, hval] using h'
  have hA1_inv : cfcR (fun x : ℝ ↦ x⁻¹) A1 = Ring.inverse A1 := by
    dsimp [cfcR]
    simpa [cfc_id' (R := ℝ) (a := A1) (ha := hA1_sa)] using
      (cfc_inv (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (f := fun x : ℝ ↦ x)
        (a := A1) (fun x hx ↦ ne_of_gt (specA1 hx)) (ha := hA1_sa))
  have hB1_inv : cfcR (fun x : ℝ ↦ x⁻¹) B1 = Ring.inverse B1 := by
    dsimp [cfcR]
    simpa [cfc_id' (R := ℝ) (a := B1) (ha := hB1_sa)] using
      (cfc_inv (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (f := fun x : ℝ ↦ x)
        (a := B1) (fun x hx ↦ ne_of_gt (specB1 hx)) (ha := hB1_sa))
  have hA_eq : cfcR (fun x : ℝ ↦ (x + t)⁻¹) A = cfcR (fun x : ℝ ↦ x⁻¹) A1 := by
    simp [hA_inv, hA1_inv]
  have hB_eq : cfcR (fun x : ℝ ↦ (x + t)⁻¹) B = cfcR (fun x : ℝ ↦ x⁻¹) B1 := by
    simp [hB_inv, hB1_inv]
  have specC1 : spectrum ℝ C1 ⊆ Set.Ioi (0 : ℝ) := by
    intro x hx
    have hs : spectrum ℝ (cfc shift C) = shift '' spectrum ℝ C := by
      simpa [shift] using
        (cfc_map_spectrum (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (a := C)
          (f := shift) (ha := hC))
    have hx' : x ∈ shift '' spectrum ℝ C := by
      have hx0 : x ∈ spectrum ℝ (cfc shift C) := by
        have hval : cfc shift C = C + T := by
          simpa [cfcR, shift] using hC_shift
        have hval' : cfc shift C = C1 := by
          simpa [hC1] using hval
        simpa [hval'] using hx
      simpa [hs] using hx0
    rcases hx' with ⟨y, hy, rfl⟩
    have hy0 : 0 ≤ y := spectrum_nonneg_of_nonneg C_nonneg hy
    have : 0 < y + t := add_pos_of_nonneg_of_pos hy0 ht
    simpa [Set.Ioi] using this
  have hC1_ne0 : ∀ x ∈ spectrum ℝ C1, (x : ℝ) ≠ 0 := fun x hx ↦ ne_of_gt (specC1 hx)
  have hC1_sa : IsSelfAdjoint C1 := by
    simpa [hC1] using (hC.add hT)
  have hC1_inv : cfcR (fun x : ℝ ↦ x⁻¹) C1 = Ring.inverse C1 := by
    dsimp [cfcR]
    simpa [cfc_id' (R := ℝ) (a := C1) (ha := hC1_sa)] using
      (cfc_inv (R := ℝ) (A := 𝓐) (p := IsSelfAdjoint) (f := fun x : ℝ ↦ x)
        (a := C1) hC1_ne0 (ha := hC1_sa))
  have hC_eq : cfcR (fun x : ℝ ↦ (x + t)⁻¹) C = cfcR (fun x : ℝ ↦ x⁻¹) C1 := by
    calc
      cfcR (fun x : ℝ ↦ (x + t)⁻¹) C
          = Ring.inverse (C + T) := hC_inv
      _ = Ring.inverse C1 := by simp [hC1]
      _ = cfcR (fun x : ℝ ↦ x⁻¹) C1 := by simpa using hC1_inv.symm
  have hconv :
      cfcR (fun x : ℝ ↦ x⁻¹) C1
        ≤ (1 - θ) • cfcR (fun x : ℝ ↦ x⁻¹) A1
          + θ • cfcR (fun x : ℝ ↦ x⁻¹) B1 := by
    simpa [one_div] using
      (one_div_operatorConvexOn_Ioi  (A := A1) (B := B1) (t := θ)
        hA1_sa hB1_sa hθ0 hθ1 specA1 specB1)
  -- conclude by rewriting everything to the shifted `1/x` convexity statement
  simpa [C, hC_eq, hA_eq, hB_eq] using hconv
