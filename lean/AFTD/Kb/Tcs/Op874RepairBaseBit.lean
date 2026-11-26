import AFTD.Prelude

/-!
# op874_repair_base_bit

Topic: graphs   Node: 39d6047f1de0

Provenance: helper lemma. Saturated fixed-color repair obstruction for OP-874, https://arxiv.org/abs/2610.41950, Section 2.

The matching-constant cut bits in the repair gadget.
-/

def op874_repair_base_bit : Fin 20 → Bool := ![true,false,false,true,true,false,false,true,false,false,false,false,true,false,true,false,true,true,true,true]
