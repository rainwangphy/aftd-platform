import AFTD.Prelude

/-!
# wild_joint_type_C

Topic: graphs   Node: e5a25f199aa6

Provenance: helper lemma. step towards wild_one_bad_color_mixed_moment_formula_with_context

Type-C triple {1,2,3}: contains the canonical edge {1,2} but not the isolated vertex 0.
-/

/-- Type-C triple {1,2,3}. -/
def wild_joint_type_C (q : ℕ) (hq : 3 ≤ q) : Finset (Fin (3*q)) := {⟨1, by omega⟩, ⟨2, by omega⟩, ⟨3, by omega⟩}
