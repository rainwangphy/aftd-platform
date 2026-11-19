import AFTD.Prelude

/-!
# op874_twelve_port_gap_edges

Topic: graphs   Node: 8bb5e47a1387

Provenance: helper lemma. Finite global ownership obstruction in the OP-874 campaign.

Edges of the twelve-vertex simple cubic base used for the global port-compatibility obstruction.
-/

def op874_twelve_port_gap_edges : Finset (Sym2 (Fin 12)) := {s(0,1),s(1,2),s(2,3),s(3,4),s(4,0),s(5,6),s(6,7),s(7,5),s(8,9),s(9,10),s(10,11),s(11,8),s(8,3),s(4,2),s(10,0),s(1,5),s(9,6),s(11,7)}
