import AFTD.Prelude
import AFTD.Kb.Tcs.CyclicMatrixFourierComplAdjMatrix
import AFTD.Kb.Tcs.IsSharpCyclicLabeling
import AFTD.Kb.Tcs.CyclicMatrixFourier
import AFTD.Kb.Tcs.IsWeightedPartialPermutation

/-!
# sharp_cyclic_and_compl_imp_antidiagonal

Topic: combinatorics   Node: d17cfcc5be9c

Provenance: helper lemma. arXiv:2610.31807 Proposition 4.9 -- Additive energy and Fourier complexity of graphs

If G is a simple graph on ZMod N such that both G and its complement G^c have at least one edge, and the standard cyclic labeling is sharp for both G and G^c, then the two-dimensional cyclic Fourier transform of the adjacency matrix of G vanishes whenever m + n ≠ 0.
-/

/-- Simultaneous sharpness for G and its complement implies the 2D Fourier transform is anti-diagonal. -/
theorem sharp_cyclic_and_compl_imp_antidiagonal (N : ℕ) [NeZero N]
    (G : SimpleGraph (ZMod N)) [DecidableRel G.Adj]
    (he : ∃ u v, G.Adj u v) (hec : ∃ u v, Gᶜ.Adj u v)
    (hG : is_sharp_cyclic_labeling N G (Equiv.refl (ZMod N)))
    (hGc : is_sharp_cyclic_labeling N Gᶜ (Equiv.refl (ZMod N)))
    (m n : ZMod N) (hmn : m + n ≠ 0) :
    cyclic_matrix_fourier N (G.adjMatrix ℂ) m n = 0 := by
  have hFwpp : is_weighted_partial_permutation
      (cyclic_matrix_fourier N (G.adjMatrix ℂ)) := by
    unfold is_sharp_cyclic_labeling at hG
    simp only [Equiv.refl_apply] at hG
    change is_weighted_partial_permutation
      (cyclic_matrix_fourier N (Matrix.of fun i j => if G.Adj i j then (1:ℂ) else 0)) at hG
    simpa [SimpleGraph.adjMatrix] using hG
  have hEwpp : is_weighted_partial_permutation
      (cyclic_matrix_fourier N (Gᶜ.adjMatrix ℂ)) := by
    unfold is_sharp_cyclic_labeling at hGc
    simp only [Equiv.refl_apply] at hGc
    change is_weighted_partial_permutation
      (cyclic_matrix_fourier N (Matrix.of fun i j => if Gᶜ.Adj i j then (1:ℂ) else 0)) at hGc
    simpa [SimpleGraph.adjMatrix] using hGc
  have hFrow := hFwpp.1
  have hErow := hEwpp.1
  by_contra hFmn
  have hmn' : n ≠ -m := by
    intro h
    exact hmn (by rw [h]; simp)
  have hF_mneg : cyclic_matrix_fourier N (G.adjMatrix ℂ) m (-m) = 0 := by
    by_contra h
    exact hmn' (hFrow m n (-m) hFmn h)
  have hD_mneg : ((if m = 0 ∧ -m = 0 then (N : ℂ) else 0) -
      (if m + -m = 0 then 1 else 0)) ≠ 0 := by
    by_cases hm0 : m = 0
    · subst hm0
      have hN1 : (N : ℂ) - 1 ≠ 0 := by
        have hN : (N : ℂ) ≠ 1 := by
          intro h
          have hNnat : N = 1 := by exact_mod_cast h
          have hn0 : n = 0 := by
            have : Subsingleton (ZMod N) := (ZMod.subsingleton_iff).mpr hNnat
            exact Subsingleton.elim n 0
          exact hmn (by simpa [hn0])
        exact sub_ne_zero.mpr hN
      simpa using hN1
    · simp [hm0]
  have hFc_mneg : cyclic_matrix_fourier N (Gᶜ.adjMatrix ℂ) m (-m) ≠ 0 := by
    rw [cyclic_matrix_fourier_compl_adjMatrix]
    rw [hF_mneg]
    simpa using hD_mneg
  have hDmn : ((if m = 0 ∧ n = 0 then (N : ℂ) else 0) -
      (if m + n = 0 then 1 else 0)) = 0 := by
    have : ¬ (m = 0 ∧ n = 0) := by
      rintro ⟨hm, hn⟩
      exact hmn (by rw [hm, hn]; simp)
    simp [this, hmn]
  have hFc_mn : cyclic_matrix_fourier N (Gᶜ.adjMatrix ℂ) m n ≠ 0 := by
    rw [cyclic_matrix_fourier_compl_adjMatrix]
    rw [hDmn]
    simpa using hFmn
  exact hmn' (hErow m n (-m) hFc_mn hFc_mneg)
