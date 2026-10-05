import AFTD.Prelude
import AFTD.Kb.Tcs.CczLayerSyndrome

/-!
# ccz_layer_syndrome_across_blocks

Topic: quantum   Node: 5c020fbeb1bb

Sanity check: for two CCZ gates the syndrome vanishes on a triple meeting both blocks.
-/

theorem ccz_layer_syndrome_across_blocks : ccz_layer_syndrome 2 {0, 1, 3} = 0 := by decide
