import AFTD.Prelude

/-!
# finite_field_xor_five_avoids_unit_three_seventeen

Topic: combinatorics   Node: 231f51111393

Provenance: helper lemma. OP-1482; sharp small-prime boundary of the separable XOR family

There are two Boolean functions on the field with five elements whose coordinatewise XOR colors the finite plane without a false unit triple or a true unit seventeen-term progression.
-/

theorem finite_field_xor_five_avoids_unit_three_seventeen :
    ∃ f g : ZMod 5 → Bool,
      (∀ x v : Fin 2 → ZMod 5, (∑ i : Fin 2, (v i)^2) = 1 →
        ¬ ∀ k : Fin 3, xor (f (x 0 + (k.val : ZMod 5)*v 0))
          (g (x 1 + (k.val : ZMod 5)*v 1)) = false) ∧
      (∀ x v : Fin 2 → ZMod 5, (∑ i : Fin 2, (v i)^2) = 1 →
        ¬ ∀ k : Fin 17, xor (f (x 0 + (k.val : ZMod 5)*v 0))
          (g (x 1 + (k.val : ZMod 5)*v 1)) = true) := by
  refine ⟨fun x => !(decide (x ∈ ({2,4} : Finset (ZMod 5)))),
    fun y => decide (y ∈ ({0,3} : Finset (ZMod 5))), ?_, ?_⟩
  · set_option maxRecDepth 32768 in
      set_option maxHeartbeats 3000000 in
        decide
  · set_option maxRecDepth 32768 in
      set_option maxHeartbeats 3000000 in
        decide
