import AFTD.Prelude
import AFTD.Kb.Tcs.SubadditiveFWeight

/-!
# subadditive_f_weight_hasDerivAt_facts

Topic: information   Node: b7cf1420aca0

Provenance: helper lemma. arXiv:2610.21231 (On the subadditivity of mutual f-information), Appendix B, proof of Lemma 4

If f is C⁴ on (0, ∞), then at every x > 0, f, f', g = x² f'' and g' have derivatives f', f'', g', g'' at x.
-/

theorem subadditive_f_weight_hasDerivAt_facts (f : ℝ → ℝ) (hsmooth : ContDiffOn ℝ 4 f (Set.Ioi 0)) :
    ∀ x > (0:ℝ), HasDerivAt f (deriv f x) x ∧ HasDerivAt (deriv f) (deriv (deriv f) x) x ∧
      HasDerivAt (subadditive_f_weight f) (deriv (subadditive_f_weight f) x) x ∧
      HasDerivAt (deriv (subadditive_f_weight f)) (deriv (deriv (subadditive_f_weight f)) x) x := by
  intro x hx
  have hn : Set.Ioi (0:ℝ) ∈ nhds x := Ioi_mem_nhds hx
  have h1 : ContDiffOn ℝ 3 (deriv f) (Set.Ioi 0) :=
    hsmooth.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have h2 : ContDiffOn ℝ 2 (deriv (deriv f)) (Set.Ioi 0) :=
    h1.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hg : ContDiffOn ℝ 2 (subadditive_f_weight f) (Set.Ioi 0) := by
    have : subadditive_f_weight f = fun x => x ^ 2 * deriv (deriv f) x := rfl
    rw [this]
    exact (contDiffOn_id.pow 2).mul h2
  have hg1 : ContDiffOn ℝ 1 (deriv (subadditive_f_weight f)) (Set.Ioi 0) :=
    hg.deriv_of_isOpen isOpen_Ioi (by norm_num)
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact ((hsmooth.differentiableOn (by norm_num)).differentiableAt hn).hasDerivAt
  · exact ((h1.differentiableOn (by norm_num)).differentiableAt hn).hasDerivAt
  · exact ((hg.differentiableOn (by norm_num)).differentiableAt hn).hasDerivAt
  · exact ((hg1.differentiableOn (by norm_num)).differentiableAt hn).hasDerivAt
