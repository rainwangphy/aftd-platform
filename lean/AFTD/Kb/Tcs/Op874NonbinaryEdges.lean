import AFTD.Prelude

/-!
# op874_nonbinary_edges

Topic: graphs   Node: f4138662aa99

Provenance: helper lemma. Finite global ownership nonbinary obstruction in the OP-874 campaign.

The edges of the sixteen-vertex global ownership example.
-/

def op874_nonbinary_edges : Finset (Sym2 (Fin 16)) := {s(0,1),s(0,3),s(0,6),s(1,2),s(1,15),s(2,3),s(2,13),s(3,8),s(4,5),s(4,9),s(4,14),s(5,6),s(5,12),s(6,7),s(7,8),s(7,10),s(8,9),s(9,11),s(10,11),s(10,12),s(11,12),s(13,14),s(13,15),s(14,15)}
