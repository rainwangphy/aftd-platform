import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.WvgWins
import AFTD.Kb.GameTheoryEconomics.InStdSimplex
import AFTD.Kb.GameTheoryEconomics.Bz3Props
import AFTD.Kb.GameTheoryEconomics.Bz3Coal
import AFTD.Kb.GameTheoryEconomics.Bz3Pattern
import AFTD.Kb.GameTheoryEconomics.Bz3BoolImp

/-!
# bz3_props_pattern

Topic: general_equilibrium   Node: 8f299af109fb

The winning pattern of a 3-player game with simplex weights and strict quota 1/2 satisfies bz3_props.
-/

lemma bz3_props_pattern (w : Fin 3 → ℝ) (hw : in_std_simplex w) :
    bz3_props (bz3_pattern w) = true := by
  obtain ⟨h0, h1⟩ := hw
  rw [Fin.sum_univ_three] at h1
  have a := h0 0; have b := h0 1; have c := h0 2
  simp only [bz3_props, Bool.and_eq_true, bz3_bool_imp, Bool.not_eq_true']
  simp only [bz3_pattern, decide_eq_true_eq, decide_eq_false_iff_not]
  simp [bz3_coal, Finset.sum_insert, wvg_wins]
  constructorm* _ ∧ _ <;> intros <;> linarith
