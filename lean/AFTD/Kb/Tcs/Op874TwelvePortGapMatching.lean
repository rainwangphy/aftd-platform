import AFTD.Prelude

/-!
# op874_twelve_port_gap_matching

Topic: graphs   Node: 162bc8386a64

Provenance: helper lemma. Finite global ownership obstruction in the OP-874 campaign.

The six matching edges of the twelve-vertex port-compatibility base.
-/

def op874_twelve_port_gap_matching : Finset (Sym2 (Fin 12)) := {s(8,3),s(4,2),s(10,0),s(1,5),s(9,6),s(11,7)}
