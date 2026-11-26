import AFTD.Prelude
import AFTD.Kb.Tcs.QutritRationalCandidateExtension
import AFTD.Kb.Tcs.QutritRationalCandidateExtensionBlocks

/-!
# qutrit_rational_extension_omega_2_residual_certificate

Topic: quantum   Node: f1adb055e65b

Provenance: helper lemma. Exact residual certificate for the rational two-copy extension, experiment 41047; OP-2299.

The omega_2 extension block has a Hermitian diagonally dominant integer residual and the displayed exact factorization.
-/

open scoped Matrix
set_option maxHeartbeats 4000000

theorem qutrit_rational_extension_omega_2_residual_certificate :
    let v : Fin 6 → Fin 3 × Fin 3 × Fin 3 := ![(0, 0, 2), (0, 1, 1), (1, 0, 1), (1, 2, 2), (2, 0, 0), (2, 1, 2)]
    let H : Matrix (Fin 6) (Fin 6) ℂ := fun i j => qutrit_rational_candidate_extension ((v i).1, ![(v i).2.1, (v i).2.2]) ((v j).1, ![(v j).2.1, (v j).2.2])
    let B : Matrix (Fin 6) (Fin 6) ℂ := !![(3532510863 : ℂ), 0, 0, 0, 0, 0;
      (244860393 : ℂ) + (424691688 : ℂ) * Complex.I, (2472580101 : ℂ), 0, 0, 0, 0;
      (-710744311 : ℂ) + (612308945 : ℂ) * Complex.I, (-1919944832 : ℂ) + (403822141 : ℂ) * Complex.I, (2783755162 : ℂ), 0, 0, 0;
      (-406429323 : ℂ) + (-1536943044 : ℂ) * Complex.I, (684199221 : ℂ) + (-1068285988 : ℂ) * Complex.I, (1171874230 : ℂ) + (-580425041 : ℂ) * Complex.I, (712072551 : ℂ), 0, 0;
      (-1319516961 : ℂ) + (-410546508 : ℂ) * Complex.I, (581152105 : ℂ) + (964697036 : ℂ) * Complex.I, (-501466485 : ℂ) + (-1595746105 : ℂ) * Complex.I, (93541276 : ℂ) + (-145760276 : ℂ) * Complex.I, (589957724 : ℂ), 0;
      (-710744311 : ℂ) + (-612308945 : ℂ) * Complex.I, (-405099252 : ℂ) + (2134349866 : ℂ) * Complex.I, (-1537711806 : ℂ) + (1877623370 : ℂ) * Complex.I, (-620821844 : ℂ) + (-58417433 : ℂ) * Complex.I, (214984209 : ℂ) + (-264846073 : ℂ) * Complex.I, (695541080 : ℂ)]
    let R : Matrix (Fin 6) (Fin 6) ℂ := !![(35920002786995231 : ℂ), (1809050841 : ℂ) + (1285806744 : ℂ) * Complex.I, (-577049607 : ℂ) + (-275430465 : ℂ) * Complex.I, (-1460764251 : ℂ) + (1257713028 : ℂ) * Complex.I, (-1354752657 : ℂ) + (723283596 : ℂ) * Complex.I, (-577049607 : ℂ) + (275430465 : ℂ) * Complex.I;
      (1809050841 : ℂ) + (-1285806744 : ℂ) * Complex.I, (35920002222426006 : ℂ), (-1494586905 : ℂ) + (264918594 : ℂ) * Complex.I, (508420890 : ℂ) + (1359186144 : ℂ) * Complex.I, (648388572 : ℂ) + (925343160 : ℂ) * Complex.I, (168707835 : ℂ) + (-491511951 : ℂ) * Complex.I;
      (-577049607 : ℂ) + (275430465 : ℂ) * Complex.I, (-1494586905 : ℂ) + (-264918594 : ℂ) * Complex.I, (35919998807143905 : ℂ), (965458047 : ℂ) + (-1736732868 : ℂ) * Complex.I, (183698043 : ℂ) + (224613366 : ℂ) * Complex.I, (-1726657894 : ℂ) + (-650794250 : ℂ) * Complex.I;
      (-1460764251 : ℂ) + (-1257713028 : ℂ) * Complex.I, (508420890 : ℂ) + (-1359186144 : ℂ) * Complex.I, (965458047 : ℂ) + (1736732868 : ℂ) * Complex.I, (35920001686040568 : ℂ), (1379934777 : ℂ) + (1103489385 : ℂ) * Complex.I, (-652428139 : ℂ) + (-1507215568 : ℂ) * Complex.I;
      (-1354752657 : ℂ) + (-723283596 : ℂ) * Complex.I, (648388572 : ℂ) + (-925343160 : ℂ) * Complex.I, (183698043 : ℂ) + (-224613366 : ℂ) * Complex.I, (1379934777 : ℂ) + (-1103489385 : ℂ) * Complex.I, (35920002305723316 : ℂ), (-2270931587 : ℂ) + (926263775 : ℂ) * Complex.I;
      (-577049607 : ℂ) + (-275430465 : ℂ) * Complex.I, (168707835 : ℂ) + (491511951 : ℂ) * Complex.I, (-1726657894 : ℂ) + (650794250 : ℂ) * Complex.I, (-652428139 : ℂ) + (1507215568 : ℂ) * Complex.I, (-2270931587 : ℂ) + (-926263775 : ℂ) * Complex.I, (35920002970693023 : ℂ)]
    R.IsHermitian ∧
    (∀ i, (∑ j ∈ Finset.univ.erase i, (|(R i j).re| + |(R i j).im|)) ≤ (R i i).re) ∧
    ((360000000000000000000 : ℂ) • H = B * Bᴴ + R) := by
  dsimp only
  have hH : ∀ i j : Fin 6, qutrit_rational_candidate_extension
      (((![(0, 0, 2), (0, 1, 1), (1, 0, 1), (1, 2, 2), (2, 0, 0), (2, 1, 2)] : Fin 6 → Fin 3 × Fin 3 × Fin 3) i).1,
        ![((![(0, 0, 2), (0, 1, 1), (1, 0, 1), (1, 2, 2), (2, 0, 0), (2, 1, 2)] : Fin 6 → Fin 3 × Fin 3 × Fin 3) i).2.1,
          ((![(0, 0, 2), (0, 1, 1), (1, 0, 1), (1, 2, 2), (2, 0, 0), (2, 1, 2)] : Fin 6 → Fin 3 × Fin 3 × Fin 3) i).2.2])
      (((![(0, 0, 2), (0, 1, 1), (1, 0, 1), (1, 2, 2), (2, 0, 0), (2, 1, 2)] : Fin 6 → Fin 3 × Fin 3 × Fin 3) j).1,
        ![((![(0, 0, 2), (0, 1, 1), (1, 0, 1), (1, 2, 2), (2, 0, 0), (2, 1, 2)] : Fin 6 → Fin 3 × Fin 3 × Fin 3) j).2.1,
          ((![(0, 0, 2), (0, 1, 1), (1, 0, 1), (1, 2, 2), (2, 0, 0), (2, 1, 2)] : Fin 6 → Fin 3 × Fin 3 × Fin 3) j).2.2])
      = qutrit_rational_candidate_extension_blocks 2 (![(2:Fin 6), 3, 1, 5, 0, 4] i) (![(2:Fin 6), 3, 1, 5, 0, 4] j) := by
    intro i j
    fin_cases i <;> fin_cases j <;> rfl
  have hHm : (fun i j : Fin 6 => qutrit_rational_candidate_extension
      (((![(0, 0, 2), (0, 1, 1), (1, 0, 1), (1, 2, 2), (2, 0, 0), (2, 1, 2)] : Fin 6 → Fin 3 × Fin 3 × Fin 3) i).1,
        ![((![(0, 0, 2), (0, 1, 1), (1, 0, 1), (1, 2, 2), (2, 0, 0), (2, 1, 2)] : Fin 6 → Fin 3 × Fin 3 × Fin 3) i).2.1,
          ((![(0, 0, 2), (0, 1, 1), (1, 0, 1), (1, 2, 2), (2, 0, 0), (2, 1, 2)] : Fin 6 → Fin 3 × Fin 3 × Fin 3) i).2.2])
      (((![(0, 0, 2), (0, 1, 1), (1, 0, 1), (1, 2, 2), (2, 0, 0), (2, 1, 2)] : Fin 6 → Fin 3 × Fin 3 × Fin 3) j).1,
        ![((![(0, 0, 2), (0, 1, 1), (1, 0, 1), (1, 2, 2), (2, 0, 0), (2, 1, 2)] : Fin 6 → Fin 3 × Fin 3 × Fin 3) j).2.1,
          ((![(0, 0, 2), (0, 1, 1), (1, 0, 1), (1, 2, 2), (2, 0, 0), (2, 1, 2)] : Fin 6 → Fin 3 × Fin 3 × Fin 3) j).2.2]))
      = Matrix.of (fun i j : Fin 6 => qutrit_rational_candidate_extension_blocks 2
          (![(2:Fin 6), 3, 1, 5, 0, 4] i) (![(2:Fin 6), 3, 1, 5, 0, 4] j)) := by
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
