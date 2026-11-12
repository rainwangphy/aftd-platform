import AFTD.Prelude
import AFTD.Kb.Optimization.IsWolfeCorral

/-!
# singleton_is_wolfe_corral

Topic: submodular   Node: 14dbf7b275b1

Provenance: helper lemma. arXiv:2611.12680 Sec. 2.2

For any point p in ℝ^n, the singleton set {p} is a corral with affine minimizer p.
-/

/-- Every singleton set {p} is a corral with affine minimizer p. -/
theorem singleton_is_wolfe_corral {n : ℕ} (p : Fin n → ℝ) :
    is_wolfe_corral {p} p := by
  refine ⟨Finset.singleton_nonempty p, ?_, fun _ => 1, ?_, ?_, ?_⟩
  · intro q hq
    rw [Finset.mem_singleton.mp hq]
    simp
  · simp
  · intro q _
    exact Real.zero_lt_one
  · simp
