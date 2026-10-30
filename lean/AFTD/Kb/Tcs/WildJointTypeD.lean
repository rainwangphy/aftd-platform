import AFTD.Prelude

/-!
# wild_joint_type_D

Topic: graphs   Node: 90dfa2e08df0

Provenance: helper lemma. step towards wild_one_bad_color_mixed_moment_formula_with_context

Type-D triple {1,3,5}: contains neither the isolated vertex 0 nor a canonical edge (three vertices from distinct pairs).
-/

/-- Type-D triple {1,3,5}. -/
def wild_joint_type_D (q : ℕ) (hq : 3 ≤ q) : Finset (Fin (3*q)) := {⟨1, by omega⟩, ⟨3, by omega⟩, ⟨5, by omega⟩}
