import AFTD.Prelude

/-!
# sixteen_spin_diff_pattern

Topic: quantum_mechanics   Node: 7db50141074b

Provenance: helper lemma. step towards op_1695_pi_over_eight_eq_bipartite_subgraphs

For a sixteen-spin configuration sp : V → Fin 4 → Fin 2, the π/8 difference pattern on an unordered pair of vertices is the predicate that spin components 1 and 3 differ across the pair while component 2 agrees (component 0 is unconstrained).
-/

/-- The Sym2-lifted predicate "component 1 differs, component 2 agrees, component 3 differs" on an unordered pair of vertices. -/
def sixteen_spin_diff_pattern {V : Type*} (sp : V → Fin 4 → Fin 2) : Sym2 V → Prop := Sym2.lift ⟨fun u v => sp u 1 ≠ sp v 1 ∧ sp u 2 = sp v 2 ∧ sp u 3 ≠ sp v 3, by
    intro u v; rw [eq_iff_iff]; tauto⟩
