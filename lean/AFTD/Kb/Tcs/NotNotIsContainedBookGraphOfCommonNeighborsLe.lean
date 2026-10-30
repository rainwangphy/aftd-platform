import AFTD.Prelude
import AFTD.Kb.Tcs.BookGraph

/-!
# not_not_isContained_book_graph_of_commonNeighbors_le

Topic: combinatorics   Node: f1f8ed40a51f

Provenance: original. Related work: refutes `not_isContained_book_graph_of_commonNeighbors_le`

The statement `not_isContained_book_graph_of_commonNeighbors_le` is false: The statement is FALSE for k = 0.
Under Lean's `Nat` subtraction, 0 - 1 = 0.
When k = 0, the hypothesis `h` requires that every pair of adjacent vertices u, v in G has at most 0 - 1 = 0 common neighbors, which holds for any triangle-free graph, such as the complete graph G = K_2 on two vertices.
However, `book_graph 0` is the book graph with 0 pages, whose vertex set is `Fin 2 ⊕ Fin 0 ≃ Fin 2`, consisting solely of the single edge between `Sum.inl 0` and `Sum.inl 1`.
Thus `book_graph 0` is isomorphic to K_2, which is contained in G = K_2.
Therefore, `(book_graph 0).IsContained G` holds, contradicting `¬ (book_graph 0).IsContained G`.
-/

theorem not_not_isContained_book_graph_of_commonNeighbors_le : ¬ (∀ {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : ℕ)
    (h : ∀ u v : V, G.Adj u v → Fintype.card (G.commonNeighbors u v) ≤ k - 1), ¬ (book_graph k).IsContained G) := by
  intro H
  open SimpleGraph in
  have hc : (book_graph 0).IsContained (⊤ : SimpleGraph (ULift (Fin 2))) := by
    refine ⟨⟨⟨fun x => match x with | Sum.inl i => ⟨i⟩ | Sum.inr i => i.elim0, ?_⟩, ?_⟩⟩
    · rintro (x | x) (y | y) h
      · rw [top_adj]
        intro heq
        exact h (ULift.ext_iff.mp heq)
      · exact y.elim0
      · exact x.elim0
      · exact x.elim0
    · rintro (x | x) (y | y) h
      · congr
        exact ULift.ext_iff.mp h
      · exact y.elim0
      · exact x.elim0
      · exact x.elim0
  have hh : ∀ u v : ULift (Fin 2), (⊤ : SimpleGraph (ULift (Fin 2))).Adj u v →
      Fintype.card ((⊤ : SimpleGraph (ULift (Fin 2))).commonNeighbors u v) ≤ 0 - 1 := by
    intro ⟨u⟩ ⟨v⟩ huv
    have : IsEmpty ((⊤ : SimpleGraph (ULift (Fin 2))).commonNeighbors ⟨u⟩ ⟨v⟩) := by
      refine ⟨fun ⟨⟨w⟩, hw⟩ => ?_⟩
      simp only [SimpleGraph.commonNeighbors, Set.mem_inter_iff, SimpleGraph.mem_neighborSet,
        SimpleGraph.top_adj] at hw
      fin_cases u <;> fin_cases v <;> fin_cases w <;> tauto
    rw [Fintype.card_eq_zero]
  exact @H (ULift (Fin 2)) _ _ ⊤ _ 0 hh hc
