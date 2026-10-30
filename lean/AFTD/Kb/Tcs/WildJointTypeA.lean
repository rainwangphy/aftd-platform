import AFTD.Prelude

/-!
# wild_joint_type_A

Topic: graphs   Node: d8140910db93

Provenance: helper lemma. step towards wild_one_bad_color_mixed_moment_formula_with_context

Type-A triple {0,1,2}: contains the isolated vertex 0 and the canonical edge {1,2}; immediately whole-bad, so alpha at it is 1.
-/

/-- Type-A triple {0,1,2}. -/
def wild_joint_type_A (q : ℕ) (hq : 3 ≤ q) : Finset (Fin (3*q)) := {⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩}
