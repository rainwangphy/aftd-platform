import AFTD.Prelude
import AFTD.Kb.Tcs.IsASPath
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Physics.WaveEquationZero

/-!
# isASPath_id

Topic: combinatorics   Node: 751835ba0763

Provenance: helper lemma. arXiv:2611.12329 Piercing a Chessboard with Restricted Slopes, Eq. (1)

The identity function a(t) = t is an ascending shallow path coordinate function.
-/

/-- The identity function is an AS path coordinate function. -/
theorem isASPath_id : IsASPath (fun t => t) := by first | exact wave_equation_zero | (apply wave_equation_zero <;> assumption) | (apply wave_equation_zero <;> simp_all) | simpa using wave_equation_zero | (simp only [IsASPath] at *; first | exact wave_equation_zero | (apply wave_equation_zero <;> assumption) | (apply wave_equation_zero <;> simp_all) | simpa using wave_equation_zero)
