import AFTD.Prelude
import AFTD.Kb.Tcs.QutritRationalCandidateExtension
import AFTD.Kb.Tcs.QutritRationalCandidateExtensionBlocks

/-!
# qutrit_rational_extension_omega_0_residual_certificate

Topic: quantum   Node: cfaf67162b2e

Provenance: helper lemma. Exact residual certificate for the rational two-copy extension, experiment 41047; OP-2299.

The omega_0 extension block has a Hermitian diagonally dominant integer residual and the displayed exact factorization.
-/

open scoped Matrix
set_option maxHeartbeats 4000000

theorem qutrit_rational_extension_omega_0_residual_certificate :
    let v : Fin 6 → Fin 3 × Fin 3 × Fin 3 := ![(0, 0, 0), (0, 1, 2), (1, 0, 2), (1, 1, 1), (2, 0, 1), (2, 2, 2)]
    let H : Matrix (Fin 6) (Fin 6) ℂ := fun i j => qutrit_rational_candidate_extension ((v i).1, ![(v i).2.1, (v i).2.2]) ((v j).1, ![(v j).2.1, (v j).2.2])
    let B : Matrix (Fin 6) (Fin 6) ℂ := !![(9421330692 : ℂ), 0, 0, 0, 0, 0;
      (657403949 : ℂ) + (1600207072 : ℂ) * Complex.I, (5480504482 : ℂ), 0, 0, 0, 0;
      (-1296841327 : ℂ) + (-4656354971 : ℂ) * Complex.I, (444623442 : ℂ) + (455252156 : ℂ) * Complex.I, (3043088632 : ℂ), 0, 0, 0;
      (883174604 : ℂ) + (-2474917903 : ℂ) * Complex.I, (-2139736475 : ℂ) + (2463751849 : ℂ) * Complex.I, (-1431240042 : ℂ) + (-8040380909 : ℂ) * Complex.I, (2124037997 : ℂ), 0, 0;
      (-1603448015 : ℂ) + (-1110492811 : ℂ) * Complex.I, (-553925009 : ℂ) + (-610331860 : ℂ) * Complex.I, (-4138244052 : ℂ) + (2482478619 : ℂ) * Complex.I, (379221480 : ℂ) + (-2243133404 : ℂ) * Complex.I, (286310948 : ℂ), 0;
      (883174604 : ℂ) + (2474917903 : ℂ) * Complex.I, (-3057921886 : ℂ) + (7965562584 : ℂ) * Complex.I, (-1545763778 : ℂ) + (1520074023 : ℂ) * Complex.I, (-1173613728 : ℂ) + (-1682749930 : ℂ) * Complex.I, (90909057 : ℂ) + (-300185995 : ℂ) * Complex.I, (218584420 : ℂ)]
    let R : Matrix (Fin 6) (Fin 6) ℂ := !![(3567991978801136 : ℂ), (-1755702708 : ℂ) + (989053824 : ℂ) * Complex.I, (-3280891716 : ℂ) + (-1129069932 : ℂ) * Complex.I, (-3060145968 : ℂ) + (285821124 : ℂ) * Complex.I, (-3254023620 : ℂ) + (-3519655212 : ℂ) * Complex.I, (-3060145968 : ℂ) + (-285821124 : ℂ) * Complex.I;
      (-1755702708 : ℂ) + (-989053824 : ℂ) * Complex.I, (3567997338303891 : ℂ), (-2750511809 : ℂ) + (-1755752743 : ℂ) * Complex.I, (210279770 : ℂ) + (965688783 : ℂ) * Complex.I, (1160960965 : ℂ) + (-337545079 : ℂ) * Complex.I, (-1497228160 : ℂ) + (-985099053 : ℂ) * Complex.I;
      (-3280891716 : ℂ) + (1129069932 : ℂ) * Complex.I, (-2750511809 : ℂ) + (1755752743 : ℂ) * Complex.I, (3568003702261106 : ℂ), (1827726745 : ℂ) + (4863041635 : ℂ) * Complex.I, (-1972961384 : ℂ) + (2171934124 : ℂ) * Complex.I, (665697525 : ℂ) + (4289166083 : ℂ) * Complex.I;
      (-3060145968 : ℂ) + (-285821124 : ℂ) * Complex.I, (210279770 : ℂ) + (-965688783 : ℂ) * Complex.I, (1827726745 : ℂ) + (-4863041635 : ℂ) * Complex.I, (3568004027581295 : ℂ), (611100519 : ℂ) + (2533383698 : ℂ) * Complex.I, (-4068798026 : ℂ) + (3933453260 : ℂ) * Complex.I;
      (-3254023620 : ℂ) + (3519655212 : ℂ) * Complex.I, (1160960965 : ℂ) + (337545079 : ℂ) * Complex.I, (-1972961384 : ℂ) + (-2171934124 : ℂ) * Complex.I, (611100519 : ℂ) + (-2533383698 : ℂ) * Complex.I, (3567999298966188 : ℂ), (921182650 : ℂ) + (3528269697 : ℂ) * Complex.I;
      (-3060145968 : ℂ) + (285821124 : ℂ) * Complex.I, (-1497228160 : ℂ) + (985099053 : ℂ) * Complex.I, (665697525 : ℂ) + (-4289166083 : ℂ) * Complex.I, (-4068798026 : ℂ) + (-3933453260 : ℂ) * Complex.I, (921182650 : ℂ) + (-3528269697 : ℂ) * Complex.I, (3568012614165352 : ℂ)]
    R.IsHermitian ∧
    (∀ i, (∑ j ∈ Finset.univ.erase i, (|(R i j).re| + |(R i j).im|)) ≤ (R i i).re) ∧
    ((1800000000000000000000 : ℂ) • H = B * Bᴴ + R) := by
  dsimp only
  have hH : ∀ i j : Fin 6, qutrit_rational_candidate_extension
      (((![(0, 0, 0), (0, 1, 2), (1, 0, 2), (1, 1, 1), (2, 0, 1), (2, 2, 2)] : Fin 6 → Fin 3 × Fin 3 × Fin 3) i).1,
        ![((![(0, 0, 0), (0, 1, 2), (1, 0, 2), (1, 1, 1), (2, 0, 1), (2, 2, 2)] : Fin 6 → Fin 3 × Fin 3 × Fin 3) i).2.1,
          ((![(0, 0, 0), (0, 1, 2), (1, 0, 2), (1, 1, 1), (2, 0, 1), (2, 2, 2)] : Fin 6 → Fin 3 × Fin 3 × Fin 3) i).2.2])
      (((![(0, 0, 0), (0, 1, 2), (1, 0, 2), (1, 1, 1), (2, 0, 1), (2, 2, 2)] : Fin 6 → Fin 3 × Fin 3 × Fin 3) j).1,
        ![((![(0, 0, 0), (0, 1, 2), (1, 0, 2), (1, 1, 1), (2, 0, 1), (2, 2, 2)] : Fin 6 → Fin 3 × Fin 3 × Fin 3) j).2.1,
          ((![(0, 0, 0), (0, 1, 2), (1, 0, 2), (1, 1, 1), (2, 0, 1), (2, 2, 2)] : Fin 6 → Fin 3 × Fin 3 × Fin 3) j).2.2])
      = qutrit_rational_candidate_extension_blocks 0 (![(0:Fin 6),4,2,3,1,5] i) (![(0:Fin 6),4,2,3,1,5] j) := by
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  have hHm : (fun i j : Fin 6 => qutrit_rational_candidate_extension
      (((![(0, 0, 0), (0, 1, 2), (1, 0, 2), (1, 1, 1), (2, 0, 1), (2, 2, 2)] : Fin 6 → Fin 3 × Fin 3 × Fin 3) i).1,
        ![((![(0, 0, 0), (0, 1, 2), (1, 0, 2), (1, 1, 1), (2, 0, 1), (2, 2, 2)] : Fin 6 → Fin 3 × Fin 3 × Fin 3) i).2.1,
          ((![(0, 0, 0), (0, 1, 2), (1, 0, 2), (1, 1, 1), (2, 0, 1), (2, 2, 2)] : Fin 6 → Fin 3 × Fin 3 × Fin 3) i).2.2])
      (((![(0, 0, 0), (0, 1, 2), (1, 0, 2), (1, 1, 1), (2, 0, 1), (2, 2, 2)] : Fin 6 → Fin 3 × Fin 3 × Fin 3) j).1,
        ![((![(0, 0, 0), (0, 1, 2), (1, 0, 2), (1, 1, 1), (2, 0, 1), (2, 2, 2)] : Fin 6 → Fin 3 × Fin 3 × Fin 3) j).2.1,
          ((![(0, 0, 0), (0, 1, 2), (1, 0, 2), (1, 1, 1), (2, 0, 1), (2, 2, 2)] : Fin 6 → Fin 3 × Fin 3 × Fin 3) j).2.2]))
      = Matrix.of (fun i j : Fin 6 => qutrit_rational_candidate_extension_blocks 0
          (![(0:Fin 6),4,2,3,1,5] i) (![(0:Fin 6),4,2,3,1,5] j)) := by
    ext i j
    exact hH i j
  refine ⟨?_, ?_, ?_⟩
  · refine Matrix.IsHermitian.ext ?_
    intro i j
    fin_cases i <;> fin_cases j <;> simp only [Complex.ext_iff] <;> constructor <;>
      (simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
        Complex.I_re, Complex.I_im] <;> norm_num)
  · intro i
    fin_cases i <;>
      (rw [Finset.sum_erase_eq_sub (Finset.mem_univ _)] <;>
       simp [Fin.sum_univ_six] <;> norm_num)
  · rw [hHm]
    ext i j
    fin_cases i <;> fin_cases j <;> simp only [Complex.ext_iff] <;> constructor <;>
      (simp only [Matrix.smul_apply, Pi.smul_apply, smul_eq_mul, Matrix.of_apply, Matrix.add_apply,
          Matrix.mul_apply, Matrix.conjTranspose_apply, Fin.sum_univ_six]
       <;> simp [qutrit_rational_candidate_extension_blocks, qutrit_bosonic_pair_code,
          Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im,
          Complex.sub_re, Complex.sub_im, Complex.div_re, Complex.div_im,
          Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
       <;> norm_num)
