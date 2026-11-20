import AFTD.Prelude

/-!
# op1957_two_bridge_H_classes

Topic: graphs   Node: 08589d34802f

Provenance: helper lemma. step towards op1957_ten_connected_first_witness_two_bridges_obstruction

The eight H-neighbourhoods of size at least five, indexed, with 6,8,9 and 15,17,19 sharing a class.
-/

/-- Indexed list of the eight H-neighbourhoods of size at least 5 (the classes of the H-neighbourhood partition). -/
def op1957_two_bridge_H_classes : Fin 8 → Finset (Fin 20) := ![({2,3,6,7,8,9,10} : Finset (Fin 20)),
      ({2,3,14,15,17,19} : Finset (Fin 20)),
      ({0,1,3,6,7,8,9} : Finset (Fin 20)),
      ({0,1,2,6,7,8,9} : Finset (Fin 20)),
      ({0,2,3,14,15,17,19} : Finset (Fin 20)),
      ({0,2,3,15,17,19} : Finset (Fin 20)),
      ({1,6,8,9,11} : Finset (Fin 20)),
      ({1,6,7,8,9,10,11} : Finset (Fin 20))]
