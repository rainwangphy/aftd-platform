import AFTD.Prelude

/-!
# op874_repair_base_left

Topic: graphs   Node: 1a43471b0b87

Provenance: helper lemma. Saturated fixed-color repair obstruction for OP-874, https://arxiv.org/abs/2610.41950, Section 2.

Left endpoints of the twenty factor edges followed by ten matching edges in the repair gadget.
-/

def op874_repair_base_left : Fin 30 → Fin 20 := ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,0,1,2,3,6,9,10,12,14,16]
