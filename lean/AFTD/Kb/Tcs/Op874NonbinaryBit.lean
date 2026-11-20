import AFTD.Prelude

/-!
# op874_nonbinary_bit

Topic: graphs   Node: 59139a7b2c45

Provenance: helper lemma. Finite global ownership nonbinary obstruction in the OP-874 campaign.

The matching-cut bits in the global ownership example.
-/

def op874_nonbinary_bit : Fin 16 → Bool := ![true,false,false,true,true,true,true,false,true,false,false,false,true,false,true,false]
