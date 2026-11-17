import AFTD.Prelude
import AFTD.Kb.Tcs.MagicSquareGuessFnConcaveOn
import AFTD.Kb.Tcs.IsPovm
import AFTD.Kb.Tcs.MagicSquareGuessFn
import AFTD.Kb.Tcs.MagicSquareScore
import AFTD.Kb.Tcs.MagicSquareKeyGuessSuccess
import AFTD.Kb.Tcs.MagicSquareStrategyValid

/-!
# magic_square_guess_fn_le_one_on_Iic

Topic: quantum   Node: 83a97183f234

Provenance: helper lemma. arXiv:2610.12001, Section 6 and Corollary 6.2; analysis of the right-hand secant limit.

At every score threshold at most one, the supremal guessing probability is at most one.
-/

theorem magic_square_guess_fn_le_one_on_Iic {w : ℝ} (hw : w ≤ 1) : magic_square_guess_fn w ≤ 1 := by
  rw [MagicSquareConcave.g_eq]
  refine csSup_le (MagicSquareConcave.gset_nonempty hw) ?_
  rintro p ⟨dA, dB, dE, A, B, ρ, M, hv, hM, -, rfl⟩
  exact MagicSquareConcave.guess_le_one hv hM
