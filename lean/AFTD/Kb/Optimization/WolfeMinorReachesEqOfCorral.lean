import AFTD.Prelude
import AFTD.Kb.Optimization.IsWolfeCorral
import AFTD.Kb.Optimization.WolfeMinorStep
import AFTD.Kb.Optimization.IsAffineMinimizer

/-!
# wolfe_minor_reaches_eq_of_corral

Topic: submodular   Node: ed8d65052335

Provenance: helper lemma. arXiv:2611.12680 Sec. 2.2

If a support T : Finset (Fin n → ℝ) is a Wolfe corral with center w, then for any ambient weights lam : (Fin n → ℝ) → ℝ, any state final reachable from (T, lam) under the reflexive-transitive closure of wolfe_minor_step has final.1 = T.
-/

/-- If the initial support is already a corral, no minor cycle can occur and the support is preserved. -/
theorem wolfe_minor_reaches_eq_of_corral {n : ℕ}
    (T : Finset (Fin n → ℝ)) (lam : (Fin n → ℝ) → ℝ) (w : Fin n → ℝ)
    (hcorral : is_wolfe_corral T w)
    (final : Finset (Fin n → ℝ) × ((Fin n → ℝ) → ℝ))
    (hreach : Relation.ReflTransGen wolfe_minor_step (T, lam) final) :
    final.1 = T := by
  rcases Relation.ReflTransGen.cases_head hreach with rfl | ⟨c, hstep, _⟩
  · rfl
  · rcases c with ⟨T', lam'⟩
    dsimp [wolfe_minor_step] at hstep
    exact False.elim (hstep.1 ⟨w, hcorral⟩)
