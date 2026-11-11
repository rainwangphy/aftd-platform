import AFTD.Prelude

/-!
# good_slopes_f3_two_directions_line

Topic: elementary_number_theory   Node: 0321e2cb7933

Provenance: helper lemma. Fiber rigidity step for OP-1027, using the two nonzero directions in the field with three elements; compare the finite-field direction arguments in arXiv:2611.04551.

If two maps from a three-element index set to the field with three elements have the property that both y+s and y+2s are injective, then s is constant or y is constant.
-/

theorem good_slopes_f3_two_directions_line (s y : Fin 3 → ZMod 3) (h1 : Function.Injective (fun i => y i + s i)) (h2 : Function.Injective (fun i => y i + 2 * s i)) : (∀ i j, s i = s j) ∨ (∀ i j, y i = y j) := by
  have h : ∀ (s y : Fin 3 → ZMod 3), Function.Injective (fun i => y i + s i) → Function.Injective (fun i => y i + 2 * s i) → (∀ i j, s i = s j) ∨ (∀ i j, y i = y j) := by decide
  exact h s y h1 h2
