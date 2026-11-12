import AFTD.Prelude
import AFTD.Kb.Tcs.CayleyTableGraph
import AFTD.Kb.Tcs.GroupIsCompleteMapping
import AFTD.Kb.Tcs.CayleyTableGraphExistsTransversalOfChromaticNumberLeSucc
import AFTD.Kb.Tcs.CayleyTableGraphExistsCompleteMappingOfTransversal
import AFTD.Kb.Tcs.CayleyTableGraphChromaticNumberLeCardOfCompleteMapping

/-!
# group_cayley_table_chromatic_number_ne_succ

Topic: combinatorics   Node: 17fec9e74a6b

Provenance: formalization of a published result. Source: arXiv:2611.13274 Theorem 4.22 (On the Chromatic Number of Cayley Tables of Dihedral Groups)

For every finite group G, the chromatic number of its Cayley table Latin square graph is not equal to |G| + 1.
-/

/-- The chromatic number of the Cayley table Latin square graph of a finite group G is never |G| + 1. -/
theorem group_cayley_table_chromatic_number_ne_succ (G : Type*) [Group G] [Fintype G] :
    (cayley_table_graph G).chromaticNumber ≠ Fintype.card G + 1 := by
  intro h
  have hle : (cayley_table_graph G).chromaticNumber ≤ (Fintype.card G : ℕ∞) + 1 := le_of_eq h
  obtain ⟨s, hindep, hcard⟩ :=
    cayley_table_graph_exists_transversal_of_chromatic_number_le_succ G hle
  obtain ⟨θ, hθ⟩ :=
    cayley_table_graph_exists_complete_mapping_of_transversal G s hindep hcard
  have hle' : (cayley_table_graph G).chromaticNumber ≤ (Fintype.card G : ℕ∞) :=
    cayley_table_graph_chromatic_number_le_card_of_complete_mapping G θ hθ
  rw [h] at hle'
  have key : ((Fintype.card G + 1 : ℕ) : ℕ∞) ≤ (Fintype.card G : ℕ∞) := by
    simpa using hle'
  exact absurd (ENat.natCast_le_natCast.mp key) (by omega)
