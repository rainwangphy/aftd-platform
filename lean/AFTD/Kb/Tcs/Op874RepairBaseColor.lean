import AFTD.Prelude

/-!
# op874_repair_base_color

Topic: graphs   Node: 643c391bb466

Provenance: helper lemma. Saturated fixed-color repair obstruction for OP-874, https://arxiv.org/abs/2610.41950, Section 2.

The reference external colors on the factor and matching edges of the repair gadget.
-/

def op874_repair_base_color : Fin 30 → Fin 6 := ![4,2,5,2,4,3,2,3,4,3,5,4,2,5,3,2,4,3,2,5,1,0,0,1,0,0,0,1,1,1]
