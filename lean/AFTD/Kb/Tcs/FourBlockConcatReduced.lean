import AFTD.Prelude
import AFTD.Kb.Tcs.FourBlockConcat

/-!
# four_block_concat_reduced

Topic: information   Node: f6f6ed5ccb95

Provenance: helper lemma. arXiv:2610.29807, Lemma 3.1

For any natural number m and Boolean functions g0, g1, g2, g3 on Fin m → ZMod 2, the four-block concatenation four_block_concat g0 g1 g2 (g1 + g2 + g3) is identically equal to the function sending v to (1 + y1) * (1 + y2) * g0 x + y1 * g1 x + y2 * g2 x + y1 * y2 * g3 x, where x = fun i => v (Fin.castAdd 2 i), y1 = v (Fin.natAdd m 0), and y2 = v (Fin.natAdd m 1).
-/

/-- Over characteristic 2, the four-block concatenation g_0 || g_1 || g_2 || (g_1 + g_2 + g_3) simplifies to (1 + y_1)(1 + y_2) g_0 + y_1 g_1 + y_2 g_2 + y_1 y_2 g_3. -/
theorem four_block_concat_reduced {m : ℕ} (g0 g1 g2 g3 : (Fin m → ZMod 2) → ZMod 2) :
    four_block_concat g0 g1 g2 (g1 + g2 + g3) =
    fun v =>
      let x : Fin m → ZMod 2 := fun i => v (Fin.castAdd 2 i)
      let y1 : ZMod 2 := v (Fin.natAdd m 0)
      let y2 : ZMod 2 := v (Fin.natAdd m 1)
      (1 + y1) * (1 + y2) * g0 x + y1 * g1 x + y2 * g2 x + y1 * y2 * g3 x := by
  funext v
  simp only [four_block_concat, Pi.add_apply]
  have h2 : (2 : ZMod 2) = 0 := by decide
  ring_nf
  simp only [h2, mul_zero, add_zero]
