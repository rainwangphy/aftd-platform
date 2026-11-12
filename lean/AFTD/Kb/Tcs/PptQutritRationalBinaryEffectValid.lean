import AFTD.Prelude
import AFTD.Kb.Tcs.PptQutritRationalBinaryEffect

/-!
# ppt_qutrit_rational_binary_effect_valid

Topic: quantum   Node: aa95290ec467

Provenance: helper lemma. Helper for OP-693 and the explicit candidate; rational LDL certificates are in experiment 22884.

Each rational qutrit effect and its complement is positive semidefinite.
-/

open Matrix
open scoped ComplexOrder Matrix BigOperators
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

private noncomputable def in767_effect0 : Matrix (Fin 3) (Fin 3) ℂ := !![(1215916159000 / 21192203043001), (-2086398000000 / 21192203043001), (1071090000 / 65981951167); (-2086398000000 / 21192203043001), (3622358659000 / 21192203043001), (532050000 / 65981951167); (1071090000 / 65981951167), (532050000 / 65981951167), (7650594020 / 10066309561)]

private theorem in767_effect0_psd : in767_effect0.PosSemidef := by
  let A : Matrix (Fin 3) (Fin 3) ℂ := !![1, 0, 0; (-2086398000 / 1215916159), 1, 0; (3784160970 / 13375077749), (10180863183220951350 / 565705940444378591), 1]
  let d : Fin 3 → ℂ := ![(1215916159000 / 21192203043001), (51427812767670781000 / 25767942124793887753159), (56438373852318592032729620 / 517688283364522254480637141)]
  have hd : (diagonal d).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    fin_cases i <;> norm_num [d, Complex.nonneg_iff]
  have h := hd.mul_mul_conjTranspose_same A
  have hEq : A * diagonal d * Aᴴ = in767_effect0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [A, d, in767_effect0, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.vecMul_diagonal, map_div₀, map_ofNat, Fin.sum_univ_succ]
  exact hEq ▸ h

private noncomputable def in767_complement0 : Matrix (Fin 3) (Fin 3) ℂ := !![(19976286884001 / 21192203043001), (2086398000000 / 21192203043001), (-1071090000 / 65981951167); (2086398000000 / 21192203043001), (17569844384001 / 21192203043001), (-532050000 / 65981951167); (-1071090000 / 65981951167), (-532050000 / 65981951167), (2415715541 / 10066309561)]

private theorem in767_complement0_psd : in767_complement0.PosSemidef := by
  let A : Matrix (Fin 3) (Fin 3) ℂ := !![1, 0, 0; (695466000000 / 6658762294667), 1, 0; (-1261386990000 / 73246385241337), (-3294979200237486925850000 / 423655460931576873495549779), 1]
  let d : Fin 3 → ℂ := ![(19976286884001 / 21192203043001), (115542398435884601862422667 / 141113842563662318833975667), (92911606330607461544304200260855949 / 387695183358672204406794566481739729)]
  have hd : (diagonal d).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    fin_cases i <;> norm_num [d, Complex.nonneg_iff]
  have h := hd.mul_mul_conjTranspose_same A
  have hEq : A * diagonal d * Aᴴ = in767_complement0 := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [A, d, in767_complement0, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.vecMul_diagonal, map_div₀, map_ofNat, Fin.sum_univ_succ]
  exact hEq ▸ h

private noncomputable def in767_effect1 : Matrix (Fin 3) (Fin 3) ℂ := !![(316737473028500 / 1360728454130809), 0, 0; 0, (605951028500 / 1360728454130809), (-76179480000 / 4236629775103); 0, (-76179480000 / 4236629775103), (488260819680 / 646346857849)]

private theorem in767_effect1_psd : in767_effect1.PosSemidef := by
  let A : Matrix (Fin 3) (Fin 3) ℂ := !![1, 0, 0; 0, 1, 0; 0, (-538284205680 / 13330922627), 1]
  let d : Fin 3 → ℂ := ![(316737473028500 / 1360728454130809), (605951028500 / 1360728454130809), (22999600761798881760 / 783309086562689695393)]
  have hd : (diagonal d).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    fin_cases i <;> norm_num [d, Complex.nonneg_iff]
  have h := hd.mul_mul_conjTranspose_same A
  have hEq : A * diagonal d * Aᴴ = in767_effect1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [A, d, in767_effect1, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.vecMul_diagonal, map_div₀, map_ofNat, Fin.sum_univ_succ]
  exact hEq ▸ h

private noncomputable def in767_complement1 : Matrix (Fin 3) (Fin 3) ℂ := !![(1043990981102309 / 1360728454130809), 0, 0; 0, (1360122503102309 / 1360728454130809), (76179480000 / 4236629775103); 0, (76179480000 / 4236629775103), (158086038169 / 646346857849)]

private theorem in767_complement1_psd : in767_complement1.PosSemidef := by
  let A : Matrix (Fin 3) (Fin 3) ℂ := !![1, 0, 0; 0, 1, 0; 0, (269142102840000 / 14961347534125399), 1]
  let d : Fin 3 → ℂ := ![(1043990981102309 / 1360728454130809), (1360122503102309 / 1360728454130809), (214732015594466991886032221 / 879110906169894176726673341)]
  have hd : (diagonal d).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    fin_cases i <;> norm_num [d, Complex.nonneg_iff]
  have h := hd.mul_mul_conjTranspose_same A
  have hEq : A * diagonal d * Aᴴ = in767_complement1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [A, d, in767_complement1, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.vecMul_diagonal, map_div₀, map_ofNat, Fin.sum_univ_succ]
  exact hEq ▸ h

private noncomputable def in767_effect2 : Matrix (Fin 3) (Fin 3) ℂ := !![(1215916159000 / 21192203043001), (2086398000000 / 21192203043001), (-1071090000 / 65981951167); (2086398000000 / 21192203043001), (3622358659000 / 21192203043001), (532050000 / 65981951167); (-1071090000 / 65981951167), (532050000 / 65981951167), (7650594020 / 10066309561)]

private theorem in767_effect2_psd : in767_effect2.PosSemidef := by
  let A : Matrix (Fin 3) (Fin 3) ℂ := !![1, 0, 0; (2086398000 / 1215916159), 1, 0; (-3784160970 / 13375077749), (10180863183220951350 / 565705940444378591), 1]
  let d : Fin 3 → ℂ := ![(1215916159000 / 21192203043001), (51427812767670781000 / 25767942124793887753159), (56438373852318592032729620 / 517688283364522254480637141)]
  have hd : (diagonal d).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    fin_cases i <;> norm_num [d, Complex.nonneg_iff]
  have h := hd.mul_mul_conjTranspose_same A
  have hEq : A * diagonal d * Aᴴ = in767_effect2 := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [A, d, in767_effect2, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.vecMul_diagonal, map_div₀, map_ofNat, Fin.sum_univ_succ]
  exact hEq ▸ h

private noncomputable def in767_complement2 : Matrix (Fin 3) (Fin 3) ℂ := !![(19976286884001 / 21192203043001), (-2086398000000 / 21192203043001), (1071090000 / 65981951167); (-2086398000000 / 21192203043001), (17569844384001 / 21192203043001), (-532050000 / 65981951167); (1071090000 / 65981951167), (-532050000 / 65981951167), (2415715541 / 10066309561)]

private theorem in767_complement2_psd : in767_complement2.PosSemidef := by
  let A : Matrix (Fin 3) (Fin 3) ℂ := !![1, 0, 0; (-695466000000 / 6658762294667), 1, 0; (1261386990000 / 73246385241337), (-3294979200237486925850000 / 423655460931576873495549779), 1]
  let d : Fin 3 → ℂ := ![(19976286884001 / 21192203043001), (115542398435884601862422667 / 141113842563662318833975667), (92911606330607461544304200260855949 / 387695183358672204406794566481739729)]
  have hd : (diagonal d).PosSemidef := by
    apply Matrix.PosSemidef.diagonal
    intro i
    fin_cases i <;> norm_num [d, Complex.nonneg_iff]
  have h := hd.mul_mul_conjTranspose_same A
  have hEq : A * diagonal d * Aᴴ = in767_complement2 := by
    ext i j
    fin_cases i <;> fin_cases j <;> norm_num [A, d, in767_complement2, Matrix.mul_apply, Matrix.diagonal_apply, Matrix.vecMul_diagonal, map_div₀, map_ofNat, Fin.sum_univ_succ]
  exact hEq ▸ h


private noncomputable def in767_rational_effect (j : Fin 3) : Matrix (Fin 3) (Fin 3) ℂ :=
  if j = 0 then in767_effect0 else if j = 1 then in767_effect1 else in767_effect2

private lemma in767_comp0_eq : (1 : Matrix (Fin 3) (Fin 3) ℂ) - in767_effect0 = in767_complement0 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [in767_effect0, in767_complement0, Matrix.one_apply]

private lemma in767_comp1_eq : (1 : Matrix (Fin 3) (Fin 3) ℂ) - in767_effect1 = in767_complement1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [in767_effect1, in767_complement1, Matrix.one_apply]

private lemma in767_comp2_eq : (1 : Matrix (Fin 3) (Fin 3) ℂ) - in767_effect2 = in767_complement2 := by
  ext i j
  fin_cases i <;> fin_cases j <;> norm_num [in767_effect2, in767_complement2, Matrix.one_apply]

private theorem in767_rational_effect_valid : ∀ j, (in767_rational_effect j).PosSemidef ∧ (1 - in767_rational_effect j).PosSemidef := by
  intro j
  fin_cases j
  · simpa [in767_rational_effect, in767_comp0_eq] using And.intro in767_effect0_psd in767_complement0_psd
  · simpa [in767_rational_effect, in767_comp1_eq] using And.intro in767_effect1_psd in767_complement1_psd
  · simpa [in767_rational_effect, in767_comp2_eq] using And.intro in767_effect2_psd in767_complement2_psd

theorem ppt_qutrit_rational_binary_effect_valid : ∀ j, (ppt_qutrit_rational_binary_effect j).PosSemidef ∧ (1 - ppt_qutrit_rational_binary_effect j).PosSemidef := by
  exact in767_rational_effect_valid
