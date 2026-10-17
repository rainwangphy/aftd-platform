import AFTD.Prelude
import AFTD.Kb.Tcs.MatrixIsHermitianSpectrumSubsetIciOfSub
import AFTD.Kb.Tcs.MatrixIsHermitianSpectrumSubsetIicOfSub

/-!
# Matrix.IsHermitian.spectrum_subset_of_mem_Icc

Topic: quantum   Node: 2cfc0a536e0f

Provenance: formalization of a published result. Source: QuantumInfo, `Matrix.IsHermitian.spectrum_subset_of_mem_Icc`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/Matrix.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Matrix.IsHermitian.spectrum_subset_of_mem_Icc
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Matrix in
open BigOperators in
variable {n 𝕜 : Type*} in
variable [RCLike 𝕜] [DecidableEq n] in
open scoped ComplexOrder MatrixOrder in
open ComplexOrder in
theorem Matrix.IsHermitian.spectrum_subset_of_mem_Icc {d 𝕜 : Type*} [Fintype d] [DecidableEq d] [RCLike 𝕜]
  {A B x : Matrix d d 𝕜} (hA : A.IsHermitian) (hB : B.IsHermitian)
  (hl : (x - A).PosSemidef) (hr : (B - x).PosSemidef) :
    spectrum ℝ x ⊆ Set.Icc (⨅ i, hA.eigenvalues i) (⨆ i, hB.eigenvalues i) := by
  rw [← Set.Ici_inter_Iic]
  exact Set.subset_inter (hA.spectrum_subset_Ici_of_sub hl) (hB.spectrum_subset_Iic_of_sub hr)
