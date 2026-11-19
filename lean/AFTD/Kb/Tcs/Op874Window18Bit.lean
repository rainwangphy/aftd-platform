import AFTD.Prelude

/-!
# op874_window18_bit

Topic: graphs   Node: dab19537bfd7

Provenance: helper lemma. Eighteen-vertex fixed-cut four-window obstruction for the OP-874 campaign.

The matching-cut bits in the fixed-cut window obstruction.
-/

def op874_window18_bit : Fin 18 → Bool := ![false,false,true,true,true,true,false,true,false,true,false,false,true,false,true,true,true,false]
