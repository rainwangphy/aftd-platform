import AFTD.Prelude

/-!
# op_1370_middle

Topic: combinatorics   Node: 2c5cd1a9e343

Provenance: helper lemma. step towards op_1370_five_middle_layers_three_components_bound

The two middle layers of the power set of a five-element set: all subsets of size two or three.
-/

/-- op_1370_middle = the finset of all 2- and 3-element subsets of Fin 5 (the two middle levels). -/
def op_1370_middle : Finset (Finset (Fin 5)) := Finset.univ.filter (fun S => S.card = 2 ∨ S.card = 3)
