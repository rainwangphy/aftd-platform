import AFTD.Prelude
import AFTD.Kb.Tcs.ThreeSATToCliqueHasClique

/-!
# clique_to_vertex_cover_equivalence

Topic: np_completeness   Node: bf85797e9461

Provenance: formalization of a published result. Source: Karp (1972), 'Reducibility among combinatorial problems', Theorem 2; Gallai (1959)

Let G be a finite simple graph on vertex type V and let k ≤ |V|. Then G has a clique of size k if and only if the complement graph Gᶜ has a vertex cover of size |V| - k.
-/

/-- A graph G has a clique of size k if and only if its complement graph Gᶜ has a vertex cover of size |V| - k. -/
theorem clique_to_vertex_cover_equivalence {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (k : ℕ) (hk : k ≤ Fintype.card V) :
    ThreeSATToClique.hasClique G k ↔
      ∃ s : Finset V, s.card = Fintype.card V - k ∧ Gᶜ.IsVertexCover (s : Set V) := by
  constructor
  · rintro ⟨s, hs_card, hs_clique⟩
    refine ⟨sᶜ, ?_, ?_⟩
    · rw [Finset.card_compl, hs_card]
    · rw [Finset.coe_compl, SimpleGraph.isVertexCover_compl, ← SimpleGraph.isClique_compl, compl_compl]
      exact hs_clique
  · rintro ⟨t, ht_card, ht_cover⟩
    refine ⟨tᶜ, ?_, ?_⟩
    · rw [Finset.card_compl, ht_card, Nat.sub_sub_self hk]
    · rw [← compl_compl t, Finset.coe_compl, SimpleGraph.isVertexCover_compl,
          ← SimpleGraph.isClique_compl, compl_compl] at ht_cover
      exact ht_cover
