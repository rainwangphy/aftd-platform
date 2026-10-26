import AFTD.Prelude

/-!
# zmod8_cube_graph

Topic: combinatorics   Node: 4109c0a0683f

Provenance: helper lemma. step towards not_all_sharp_cyclic_graphs_circulant_at_powers_of_two

The cube graph Q_3 on ZMod 8, in Hankel form: x is adjacent to y iff the residue (x + y).val is 1, 3 or 5 (equivalently x ≠ y and x + y ∈ {1,3,5}, i.e. K_{4,4} minus a perfect matching).
-/

/-- The cube Q_3 on ZMod 8, given by the Hankel condition (x + y).val ∈ {1, 3, 5}. -/
def zmod8_cube_graph : SimpleGraph (ZMod 8) where
  Adj x y := (x + y).val = 1 ∨ (x + y).val = 3 ∨ (x + y).val = 5
  symm := ⟨fun x y h => by simpa [add_comm] using h⟩
  loopless := ⟨fun x h => by
    have hx : ∀ z : ZMod 8, (z + z).val ≠ 1 ∧ (z + z).val ≠ 3 ∧ (z + z).val ≠ 5 := by decide
    rcases h with h | h | h
    · exact hx x |>.1 h
    · exact hx x |>.2.1 h
    · exact hx x |>.2.2 h⟩
