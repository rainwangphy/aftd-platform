import AFTD.Prelude
import AFTD.Kb.Tcs.MatrixPiProd

/-!
# Matrix.PosSemidef.piProd

Topic: quantum   Node: 53dbe88a3f9f

Provenance: formalization of a published result. Source: QuantumInfo, `Matrix.PosSemidef.piProd`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/Matrix.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Matrix.PosSemidef.piProd
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix in
open BigOperators in
variable {n 𝕜 : Type*} in
variable [RCLike 𝕜] [DecidableEq n] in
open scoped ComplexOrder MatrixOrder in
variable {ι : Type*} {d : ι → Type*} [fι : Fintype ι] in
variable {R : Type*} in
variable {A : ∀ i, Matrix (d i) (d i) R} in
variable [DecidableEq ι] [∀ i, Fintype (d i)] in
open ComplexOrder MatrixOrder in
theorem Matrix.PosSemidef.piProd [RCLike R] (hA : ∀ i, (A i).PosSemidef) :
    (piProd A).PosSemidef := by
  -- Let B i be the square root of A i. Let BigB be the pi-product of B i. Show that BigB.conjTranspose * BigB equals the pi-product of A i using Fintype.prod_sum. Then use Matrix.PosSemidef.conjTranspose_mul_self to conclude the proof.
  obtain ⟨B, hB⟩ : ∃ B : ∀ i, Matrix (d i) (d i) R, ∀ i, (A i) = B i * star (B i) := by
    -- By definition of positive semi-definite matrices, each $A_i$ can be written as $B_i^* B_i$ for some matrix $B_i$.
    have h_decomp : ∀ i, ∃ B : Matrix (d i) (d i) R, A i = B * star B := by
      intro i
      obtain ⟨B, hB⟩ : ∃ B : Matrix (d i) (d i) R, A i = B.conjTranspose * B := by
        classical
        apply CStarAlgebra.nonneg_iff_eq_star_mul_self.mp
        exact nonneg_iff_posSemidef.mpr (hA i)
      use B.conjTranspose;
      convert hB using 1;
      simp [ Matrix.star_eq_conjTranspose ];
    exact ⟨ fun i => Classical.choose ( h_decomp i ), fun i => Classical.choose_spec ( h_decomp i ) ⟩;
  have hBigB_conjTranspose_mul_BigB : Matrix.of (fun j k : (∀ i, d i) => ∏ i, (B i * star (B i)) (j i) (k i)) = Matrix.of (fun j k : (∀ i, d i) => ∏ i, (B i) (j i) (k i)) * star (Matrix.of (fun j k : (∀ i, d i) => ∏ i, (B i) (j i) (k i))) := by
    ext j k; simp [ Matrix.mul_apply]
    simp only [Finset.prod_sum, ← Finset.prod_mul_distrib];
    refine' Finset.sum_bij ( fun p hp => fun i => p i ( Finset.mem_univ i ) ) _ _ _ _ <;> simp +decide;
    · simp [ funext_iff ];
    · exact fun b => ⟨ fun i _ => b i, rfl ⟩;
  simp only [Matrix.posSemidef_iff_dotProduct_mulVec] at hA ⊢
  simp_all [Matrix.piProd]
  constructor
  · ext1
    simp [Matrix.mul_apply, mul_comm]
  · intro x
    set y := star (Matrix.of (fun j k : (∀ i, d i) => ∏ i, B i (j i) (k i))) *ᵥ x
    convert dotProduct_star_self_nonneg y using 1
    simp only [dotProduct_mulVec, y];
    simp only [dotProduct, vecMul, Pi.star_apply, RCLike.star_def, mul_comm, star_apply, of_apply,
      star_prod];
    simp only [mul_apply, of_apply, star_apply, star_prod, RCLike.star_def, Finset.mul_sum _ _ _,
      mul_left_comm, mulVec, dotProduct, mul_comm, map_sum, map_mul, map_prod,
      RingHomCompTriple.comp_apply, RingHom.id_apply, mul_assoc];
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_comm.trans ( Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring )
