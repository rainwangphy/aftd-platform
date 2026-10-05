import AFTD.Prelude
import AFTD.Kb.Tcs.CczLayerSyndrome

/-!
# ccz_layer_syndrome_one_block

Topic: quantum   Node: 63b553f2014b

Sanity check: for two CCZ gates the syndrome is 1 on the first block {0, 1, 2}.
-/

theorem ccz_layer_syndrome_one_block : ccz_layer_syndrome 2 {0, 1, 2} = 1 := by decide
