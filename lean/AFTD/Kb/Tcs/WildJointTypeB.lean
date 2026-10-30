import AFTD.Prelude

/-!
# wild_joint_type_B

Topic: graphs   Node: fa50823865f6

Provenance: helper lemma. step towards wild_one_bad_color_mixed_moment_formula_with_context

Type-B triple {0,1,3}: contains the isolated vertex 0 but no canonical edge.
-/

/-- Type-B triple {0,1,3}. -/
def wild_joint_type_B (q : ℕ) (hq : 3 ≤ q) : Finset (Fin (3*q)) := {⟨0, by omega⟩, ⟨1, by omega⟩, ⟨3, by omega⟩}
