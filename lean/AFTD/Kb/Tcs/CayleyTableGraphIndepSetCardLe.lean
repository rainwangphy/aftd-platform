import AFTD.Prelude
import AFTD.Kb.Tcs.CayleyTableGraph

/-!
# cayley_table_graph_indep_set_card_le

Topic: combinatorics   Node: b7f8eba1345a

Provenance: helper lemma. arXiv:2611.13274 Section 1

In the Latin square graph of the Cayley table of a finite group G, every independent set (partial transversal) has cardinality at most |G|.
-/

/-- Every independent set in the Cayley table graph of a finite group has cardinality at most |G|. -/
theorem cayley_table_graph_indep_set_card_le (G : Type*) [Group G] [Fintype G]
    (s : Finset (G × G)) (h : (cayley_table_graph G).IsIndepSet (s : Set (G × G))) :
    s.card ≤ Fintype.card G := by
  rw [← Fintype.card_coe s]
  refine Fintype.card_le_of_injective (fun x : ↥s => (x.1).1) ?_
  intro x y hxy
  simp only at hxy
  by_contra hne
  have hne' : (x : G × G) ≠ (y : G × G) := by
    intro hh
    exact hne (Subtype.ext hh)
  have hadj : (cayley_table_graph G).Adj (x : G × G) (y : G × G) :=
    ⟨hne', Or.inl hxy⟩
  exact h x.2 y.2 hne' hadj
