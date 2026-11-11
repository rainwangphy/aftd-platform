import AFTD.Prelude

/-!
# good_slopes_35_rectangle_table

Topic: elementary_number_theory   Node: befd4b7d50d1

Provenance: helper lemma. Finite counting and CRT arithmetic in the OP-1027 modulus 105 reduction.

The three normalized missing-direction lists are exactly the 2-by-3 CRT rectangles with mod-5 ratios 2, 3 and 4 and mod-7 coordinates 1, 2 and 4.
-/

theorem good_slopes_35_rectangle_table :
    ∀ (r : Fin 3) (b : ZMod 35),
      (b ∈ ({1,2,3,4,6,8,9,11,12,13,16,17,18,19,22,23,24,26,27,29,31,32,33,34} : Finset (ZMod 35)) ∧
        b ∉ (if r = 0 then ({3,4,6,8,9,12,13,17,18,19,23,24,26,27,29,31,33,34} : Finset (ZMod 35))
          else if r = 1 then {2,3,4,6,9,12,13,17,19,22,24,26,27,29,31,32,33,34}
          else {2,3,6,8,12,13,17,18,19,22,23,24,26,27,31,32,33,34})) ↔
      (Nat.Coprime b.val 35 ∧ (b.val % 5 = 1 ∨ b.val % 5 = r.val + 2) ∧
        (b.val % 7 = 1 ∨ b.val % 7 = 2 ∨ b.val % 7 = 4)) := by decide
