import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutUtilityAddMonochromaticCard
import AFTD.Kb.GameTheoryEconomics.MaxcutStrongDeviationCarrier
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongEquilibrium
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongDeviation
import AFTD.Kb.GameTheoryEconomics.MaxcutUtility

/-!
# maxcut_strong_equilibrium_of_ranked_neighbors

Topic: equilibria   Node: 8ae81dc2212c

Provenance: helper lemma. Certificate helper for the OP-89 investigation, arXiv:2610.04948. Earlier-ranked colors are fixed when considering the least-ranked vertex that changes color.

A coloring is a strong equilibrium if, for every alternative color at each vertex, the earlier-ranked neighbors of that color number at least the vertex’s current monochromatic neighbors.
-/

theorem maxcut_strong_equilibrium_of_ranked_neighbors {V : Type} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (σ : V → Fin k)
    (r : V → ℕ)
    (hlock : ∀ v c, c ≠ σ v →
      (Finset.univ.filter fun w => G.Adj v w ∧ σ w = σ v).card ≤
      (Finset.univ.filter fun w => G.Adj v w ∧ r w < r v ∧ σ w = c).card) :
    is_maxcut_strong_equilibrium G σ := by
  classical
  intro S τ hdev
  have hcarrier := maxcut_strong_deviation_carrier G σ τ S hdev
  let D := Finset.univ.filter fun v => τ v ≠ σ v
  obtain ⟨v, hv, hmin⟩ := D.exists_min_image r hcarrier.1
  have hvdiff : τ v ≠ σ v := (Finset.mem_filter.mp hv).2
  have hfixed : ∀ w, r w < r v → τ w = σ w := by
    intro w hw
    by_contra hne
    have hwD : w ∈ D := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩
    have := hmin w hwD
    omega
  have hsubset : (Finset.univ.filter fun w => G.Adj v w ∧ r w < r v ∧ σ w = τ v) ⊆
      (Finset.univ.filter fun w => G.Adj v w ∧ τ w = τ v) := by
    intro w hw
    obtain ⟨_, hadj, hlt, hcolor⟩ := Finset.mem_filter.mp hw
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hadj, by rw [hfixed w hlt, hcolor]⟩
  have hmono := le_trans (hlock v (τ v) hvdiff) (Finset.card_le_card hsubset)
  have hσ := maxcut_utility_add_monochromatic_card G σ v
  have hτ := maxcut_utility_add_monochromatic_card G τ v
  have hgain := hcarrier.2.2 v hv
  omega
