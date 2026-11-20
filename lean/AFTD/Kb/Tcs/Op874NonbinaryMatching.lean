import AFTD.Prelude

/-!
# op874_nonbinary_matching

Topic: graphs   Node: dda43f9509d9

Provenance: helper lemma. Finite global ownership nonbinary obstruction in the OP-874 campaign.

The perfect matching in the global ownership example.
-/

def op874_nonbinary_matching : Finset (Sym2 (Fin 16)) := {s(3,8),s(11,9),s(1,15),s(10,7),s(14,4),s(2,13),s(6,0),s(12,5)}
