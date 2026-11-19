import AFTD.Prelude

/-!
# op874_twelve_port_gap_bit

Topic: graphs   Node: a95a31245bf4

Provenance: helper lemma. Finite global ownership obstruction in the OP-874 campaign.

The locally maximal matching cut in the twelve-vertex port-compatibility base.
-/

def op874_twelve_port_gap_bit : Fin 12 → Bool := ![false,true,true,false,true,true,false,true,false,false,false,true]
