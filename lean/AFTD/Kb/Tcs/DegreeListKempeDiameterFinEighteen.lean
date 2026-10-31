import AFTD.Prelude
import AFTD.Kb.Tcs.DegreeListKempeStep

/-!
# degree_list_kempe_diameter_fin_eighteen

Topic: graphs   Node: 8bb3eac8f90b

Provenance: helper lemma. step towards degree_list_kempe_diameter_five

For a fixed graph G on 5 vertices: every tight degree-list assignment into the fixed palette Fin 18 and every two proper L-colourings admit a Kempe chain of length at most 6.
-/

/-- Same Kempe-diameter-6 bound as `degree_list_kempe_diameter_at_most_six` but with the colour type fixed to the finite palette Fin 18. 18 is the palette bound forced by tightness: |⋃_v L v| ≤ Σ_v |L v| = Σ_v deg v = 2|E| ≤ 18. Fixing a finite palette is what turns the statement into a finite, `Decidable`-friendly object. -/
abbrev degree_list_kempe_diameter_fin_eighteen (G : SimpleGraph (Fin 5)) [DecidableRel G.Adj] : Prop := ∀ (L : Fin 5 → Finset (Fin 18)),
    (∀ v, (L v).card = G.degree v) →
    ∀ (α β : G.Coloring (Fin 18)),
      (∀ v, α v ∈ L v) → (∀ v, β v ∈ L v) →
      ∃ (k : ℕ), k ≤ 6 ∧
        ∃ (seq : List (G.Coloring (Fin 18))),
          seq ≠ [] ∧ seq.head? = some α ∧ seq.getLast? = some β ∧
          seq.length - 1 = k ∧
          seq.IsChain (degree_list_kempe_step G L)
