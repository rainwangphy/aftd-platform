import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutStrongEquilibriumExtendLowDegreeVertex
import AFTD.Kb.GameTheoryEconomics.MaxcutSingleVertexSumStrongEquilibriumExists
import AFTD.Kb.GameTheoryEconomics.MaxcutOneSumIndecomposableDeletePreconnected
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongEquilibrium

/-!
# maxcut_strong_equilibrium_reduce_connected_core

Topic: equilibria   Node: 881b00e58e85

Provenance: helper lemma. Structural reduction for OP-85, the unweighted Max-k-Cut strong-equilibrium existence problem in arXiv:2610.04948, Section 4.

Fix k. If every finite graph of minimum degree at least k whose every vertex deletion is preconnected has a strong k-color equilibrium, then every finite graph has a strong k-color equilibrium.
-/

open Finset

theorem maxcut_strong_equilibrium_reduce_connected_core (k : ℕ)
    (hbase : ∀ (V : Type) [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj],
      (∀ o : V, (G.induce ({o}ᶜ : Set V)).Preconnected) →
      (∀ v : V, k ≤ G.degree v) →
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
      by_cases hlow : ∃ v : V, G.degree v < k
      · obtain ⟨v, hv⟩ := hlow
        let A : Finset V := Finset.univ.erase v
        have hne : A ≠ Finset.univ := by
          intro he
          have hvA : v ∈ A := by rw [he]; exact mem_univ v
          simpa [A] using hvA
        have hcard : Fintype.card (↑A : Set V) < n := by
          apply lt_of_lt_of_le _ hn
          simpa using Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ A, hne⟩)
        have hex := ih _ hcard (↑A : Set V) (G.induce (↑A : Set V)) (le_refl _)
        exact maxcut_strong_equilibrium_extend_low_degree_vertex G v k hv hex
      · by_cases hs : ∃ (A B : Finset V) (o : V), A ∪ B = Finset.univ ∧ A ∩ B = {o} ∧
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
          · apply maxcut_one_sum_indecomposable_delete_preconnected G
            intro A B o hc hi hsep
            by_contra hbad
            push Not at hbad
            exact hs ⟨A, B, o, hc, hi, hsep, hbad.1, hbad.2⟩
          · intro v
            by_contra hn
            exact hlow ⟨v, by omega⟩
  intro V _ _ G _
  exact h (Fintype.card V) V G (le_refl _)
