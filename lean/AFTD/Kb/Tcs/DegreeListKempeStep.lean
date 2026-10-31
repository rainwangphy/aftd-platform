import AFTD.Prelude

/-!
# degree_list_kempe_step

Topic: graphs   Node: 38ca27f5ad8e

Provenance: helper lemma. step towards degree_list_kempe_diameter_five

The elementary L-valid Kempe change: both colourings respect every list L v, and c₂ is obtained from c₁ by swapping two distinct colours a ≠ b on a single nonempty connected component U of the subgraph induced by the a/b-coloured vertices (closed under a/b-coloured neighbours), leaving all other vertices fixed.
-/

/-- The single-step relation of degree-list Kempe reconfiguration, factored out of the target statement. Declared `abbrev` so that, after unfolding, it is definitionally the inline relation used by `degree_list_kempe_diameter_five`, making the assembly proof a plain `exact`. -/
abbrev degree_list_kempe_step (G : SimpleGraph (Fin 5)) {C : Type} [DecidableEq C] (L : Fin 5 → Finset C) (c₁ c₂ : G.Coloring C) : Prop := (∀ v, c₁ v ∈ L v) ∧ (∀ v, c₂ v ∈ L v) ∧
  ∃ (a b : C) (U : Set (Fin 5)),
    a ≠ b ∧ U.Nonempty ∧ (∀ v ∈ U, c₁ v = a ∨ c₁ v = b) ∧
    (G.induce U).Connected ∧
    (∀ u ∈ U, ∀ v : Fin 5, G.Adj u v → (c₁ v = a ∨ c₁ v = b) → v ∈ U) ∧
    (∀ v ∈ U, c₂ v = (if c₁ v = a then b else a)) ∧
    (∀ v ∉ U, c₂ v = c₁ v)
