import AFTD.Prelude

/-!
# op874_repair_base_right

Topic: graphs   Node: 9e713d40f6a5

Provenance: helper lemma. Saturated fixed-color repair obstruction for OP-874, https://arxiv.org/abs/2610.41950, Section 2.

Right endpoints of the twenty factor edges followed by ten matching edges in the repair gadget.
-/

def op874_repair_base_right : Fin 30 → Fin 20 := ![1,2,3,4,5,6,7,0,9,10,11,12,13,14,15,16,17,18,19,8,4,5,8,7,11,13,15,17,18,19]
