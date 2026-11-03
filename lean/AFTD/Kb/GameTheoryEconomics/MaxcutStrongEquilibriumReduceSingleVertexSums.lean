import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutSingleVertexSumStrongEquilibriumExists
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongEquilibrium

/-!
# maxcut_strong_equilibrium_reduce_single_vertex_sums

Topic: equilibria   Node: b0e789eab6a0

Provenance: helper lemma. Structural reduction for OP-85, the strong-equilibrium existence problem; the two-piece gluing step is maxcut_single_vertex_sum_strong_equilibrium.

For any fixed number of colors, if every finite graph with decidable equality and adjacency that has no nontrivial separation into two induced pieces meeting at one vertex has a strong equilibrium, then every finite graph with decidable equality and adjacency has a strong equilibrium. A separation is nontrivial when neither piece contains all vertices and there are no edges between the exclusive parts.
-/

open Finset

theorem maxcut_strong_equilibrium_reduce_single_vertex_sums (k : ℕ)
    (hbase : ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      (∀ (A B : Finset V) (o : V), A ∪ B = Finset.univ → A ∩ B = {o} →
        (∀ v ∈ A, v ∉ B → ∀ w ∈ B, w ∉ A → ¬ G.Adj v w) →
        A = Finset.univ ∨ B = Finset.univ) →
      ∃ σ : V → Fin k, is_maxcut_strong_equilibrium G σ) :
    ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      ∃ σ : V → Fin k, is_maxcut_strong_equilibrium G σ := by
  classical
  have h : ∀ n : ℕ, ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      Fintype.card V ≤ n → ∃ σ : V → Fin k, is_maxcut_strong_equilibrium G σ := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro V _ _ G _ hn
      by_cases hs : ∃ (A B : Finset V) (o : V), A ∪ B = Finset.univ ∧ A ∩ B = {o} ∧
          (∀ v ∈ A, v ∉ B → ∀ w ∈ B, w ∉ A → ¬ G.Adj v w) ∧
          A ≠ Finset.univ ∧ B ≠ Finset.univ
      · obtain ⟨A, B, o, hcover, hinter, hsep, hA, hB⟩ := hs
        have hcardA : Fintype.card (↑A : Set V) < n := by
          apply lt_of_lt_of_le _ hn
          simpa using Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ A, hA⟩)
        have hcardB : Fintype.card (↑B : Set V) < n := by
          apply lt_of_lt_of_le _ hn
          simpa using Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ B, hB⟩)
        have ea := ih _ hcardA (↑A : Set V) (G.induce (↑A : Set V)) (le_refl _)
        have eb := ih _ hcardB (↑B : Set V) (G.induce (↑B : Set V)) (le_refl _)
        exact maxcut_single_vertex_sum_strong_equilibrium_exists G A B o k hcover hinter hsep ea eb
      · apply hbase V G
        intro A B o hc hi hn
        by_contra hbad
        push Not at hbad
        exact hs ⟨A, B, o, hc, hi, hn, hbad.1, hbad.2⟩
  intro V _ _ G _
  exact h (Fintype.card V) V G (le_refl _)
