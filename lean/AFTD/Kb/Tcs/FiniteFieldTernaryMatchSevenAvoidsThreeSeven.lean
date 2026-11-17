import AFTD.Prelude

/-!
# finite_field_ternary_match_seven_avoids_three_seven

Topic: combinatorics   Node: a46e7b4dc128

Provenance: helper lemma. OP-1482 finite-field route; sharp boundary beyond binary separability

Two three-state coordinate functions color the plane over the field with seven elements by matching states, without a matching unit triple or a nonmatching unit seven-term progression.
-/

theorem finite_field_ternary_match_seven_avoids_three_seven :
    ∃ f g : ZMod 7 → Fin 3,
      (∀ x v : Fin 2 → ZMod 7, (∑ i : Fin 2, (v i)^2) = 1 →
        ¬ ∀ k : Fin 3, f (x 0 + (k.val : ZMod 7)*v 0) =
          g (x 1 + (k.val : ZMod 7)*v 1)) ∧
      (∀ x v : Fin 2 → ZMod 7, (∑ i : Fin 2, (v i)^2) = 1 →
        ¬ ∀ k : Fin 7, f (x 0 + (k.val : ZMod 7)*v 0) ≠
          g (x 1 + (k.val : ZMod 7)*v 1)) := by
  refine ⟨fun x => ![0,1,2,2,0,2,1] ⟨x.val, ZMod.val_lt x⟩,
    fun x => ![0,2,1,1,2,0,1] ⟨x.val, ZMod.val_lt x⟩, ?_, ?_⟩
  · set_option maxRecDepth 32768 in
      set_option maxHeartbeats 5000000 in
        decide
  · set_option maxRecDepth 32768 in
      set_option maxHeartbeats 5000000 in
        decide
