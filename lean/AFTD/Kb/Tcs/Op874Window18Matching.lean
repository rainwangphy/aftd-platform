import AFTD.Prelude

/-!
# op874_window18_matching

Topic: graphs   Node: 9e4292622525

Provenance: helper lemma. Eighteen-vertex fixed-cut four-window obstruction for the OP-874 campaign.

The perfect matching in the fixed-cut window obstruction.
-/

def op874_window18_matching : Finset (Sym2 (Fin 18)) := {s(0,10),s(1,11),s(2,9),s(3,16),s(4,14),s(5,12),s(6,17),s(7,15),s(8,13)}
