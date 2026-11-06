import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutOneDoubleDefectDeviationDecreases
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongEquilibrium
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongDeviation

/-!
# maxcut_strong_equilibrium_of_one_double_defect

Topic: equilibria   Node: eee70c8d7fe2

Provenance: helper lemma. Structural potential argument for the strong-equilibrium existence question OP-85; experiment 16416.

If a graph admits a k-coloring in which every vertex has at most two same-colored neighbors and at most one vertex has two, it has a strong equilibrium with the same property.
-/

set_option maxRecDepth 8192
set_option maxHeartbeats 3000000

theorem maxcut_strong_equilibrium_of_one_double_defect
    {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    (h : ∃ σ : V → Fin k, (∀ v : V, (Finset.univ.filter fun w => G.Adj v w ∧ σ w = σ v).card ≤ 2) ∧
      ∀ u v : V, (Finset.univ.filter fun w => G.Adj u w ∧ σ w = σ u).card = 2 → (Finset.univ.filter fun w => G.Adj v w ∧ σ w = σ v).card = 2 → u = v) :
    ∃ σ : V → Fin k, is_maxcut_strong_equilibrium G σ ∧
      (∀ v : V, (Finset.univ.filter fun w => G.Adj v w ∧ σ w = σ v).card ≤ 2) ∧
      (∀ u v : V, (Finset.univ.filter fun w => G.Adj u w ∧ σ w = σ u).card = 2 → (Finset.univ.filter fun w => G.Adj v w ∧ σ w = σ v).card = 2 → u = v) := by
  classical
  let M (ρ : V → Fin k) (v : V) : Finset V :=
    Finset.univ.filter fun w => G.Adj v w ∧ ρ w = ρ v
  let score (ρ : V → Fin k) : ℕ := ∑ v : V, (M ρ v).card
  let A : Finset (V → Fin k) := Finset.univ.filter fun ρ =>
    (∀ v, (M ρ v).card ≤ 2) ∧
      ∀ u v, (M ρ u).card = 2 → (M ρ v).card = 2 → u = v
  obtain ⟨ρ, hρ⟩ := h
  have hA : A.Nonempty := by
    refine ⟨ρ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    exact hρ
  obtain ⟨σ, hσA, hmin⟩ := Finset.exists_min_image A score hA
  have hσ : (∀ v, (M σ v).card ≤ 2) ∧
      (∀ u v, (M σ u).card = 2 → (M σ v).card = 2 → u = v) := (Finset.mem_filter.mp hσA).2
  refine ⟨σ, ?_, hσ.1, hσ.2⟩
  intro C τ hdev
  have hd := maxcut_one_double_defect_deviation_decreases G σ τ C hσ.1 hσ.2 hdev
  have hτA : τ ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hd.2⟩
  have hs : score τ < score σ := hd.1
  have hm := hmin τ hτA
  omega
