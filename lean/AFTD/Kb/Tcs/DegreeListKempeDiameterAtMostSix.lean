import AFTD.Prelude
import AFTD.Kb.Tcs.DegreeListKempeStep

/-!
# degree_list_kempe_diameter_at_most_six

Topic: graphs   Node: 076c356a84a3

Provenance: helper lemma. step towards degree_list_kempe_diameter_five

For a fixed G on 5 vertices, every tight degree-list assignment and every two proper L-colourings admit a Kempe chain of length at most 6 over an arbitrary finite colour type.
-/

/-- For a fixed graph G on Fin 5: every tight degree-list assignment (card L v = deg v) has Kempe diameter at most 6 over an arbitrary finite colour type C. This is exactly the conclusion of `degree_list_kempe_diameter_five`, with G fixed and the list hypothesis quantified over all tight L and all L-colorings. Declared `abbrev` so the target's inline body is definitionally this. -/
abbrev degree_list_kempe_diameter_at_most_six (G : SimpleGraph (Fin 5)) [DecidableRel G.Adj] : Prop := ∀ (C : Type) [Fintype C] [DecidableEq C] (L : Fin 5 → Finset C),
    (∀ v, (L v).card = G.degree v) →
    ∀ (α β : G.Coloring C),
      (∀ v, α v ∈ L v) → (∀ v, β v ∈ L v) →
      ∃ (k : ℕ), k ≤ 6 ∧
        ∃ (seq : List (G.Coloring C)),
          seq ≠ [] ∧ seq.head? = some α ∧ seq.getLast? = some β ∧
          seq.length - 1 = k ∧
          seq.IsChain (degree_list_kempe_step G L)
