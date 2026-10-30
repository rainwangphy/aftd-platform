import AFTD.Prelude

/-!
# wild_joint_color_type

Topic: graphs   Node: fbdc208a014b

Provenance: helper lemma. step towards wild_one_bad_color_mixed_moment_formula_with_context

The orbit type in {0,1,2,3} of triple T relative to colour i, where a colour-i edge inside T is an unordered pair of distinct elements of T whose A-value is i: 0 if T contains a colour-i edge and i; 1 if i but no edge; 2 if an edge but not i; 3 if neither. Equals the canonical type of the transported triple.
-/

/-- Colour-i orbit type of triple T. -/
noncomputable def wild_joint_color_type (q : ℕ) (A : Fin (3*q) → Fin (3*q) → Fin (3*q)) (T : Finset (Fin (3*q))) (i : Fin (3*q)) : ℕ := by classical exact if (∃ x ∈ T, ∃ y ∈ T, x ≠ y ∧ A x y = i) then (if i ∈ T then 0 else 2) else (if i ∈ T then 1 else 3)
