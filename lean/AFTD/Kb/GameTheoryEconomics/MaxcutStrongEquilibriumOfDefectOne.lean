import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutDefectOneStrongDeviationMonoDecreases
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongEquilibrium
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongDeviation

/-!
# maxcut_strong_equilibrium_of_defect_one

Topic: equilibria   Node: 3f519123e5ed

Provenance: helper lemma. Elementary finite potential argument for unweighted Max-k-Cut; definitions in arXiv:2610.04948, Section 1.

If a finite unweighted graph admits a k-coloring in which each vertex has at most one same-colored neighbor, it admits a strong k-color equilibrium, also with at most one same-colored neighbor per vertex.
-/

theorem maxcut_strong_equilibrium_of_defect_one
    {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    (h : ∃ σ : V → Fin k,
      ∀ v : V, (Finset.univ.filter fun w => G.Adj v w ∧ σ w = σ v).card ≤ 1) :
    ∃ σ : V → Fin k, is_maxcut_strong_equilibrium G σ ∧
      ∀ v : V, (Finset.univ.filter fun w => G.Adj v w ∧ σ w = σ v).card ≤ 1 := by
  classical
  let M (ρ : V → Fin k) (v : V) : Finset V :=
    Finset.univ.filter fun w => G.Adj v w ∧ ρ w = ρ v
  let score (ρ : V → Fin k) : ℕ := ∑ v : V, (M ρ v).card
  let A : Finset (V → Fin k) := Finset.univ.filter fun ρ => ∀ v, (M ρ v).card ≤ 1
  obtain ⟨ρ, hρ⟩ := h
  have hA : A.Nonempty := by
    refine ⟨ρ, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    exact hρ
  obtain ⟨σ, hσA, hmin⟩ := Finset.exists_min_image A score hA
  have hσ : ∀ v, (M σ v).card ≤ 1 := (Finset.mem_filter.mp hσA).2
  refine ⟨σ, ?_, hσ⟩
  intro C τ hdev
  have step := maxcut_defect_one_strong_deviation_mono_decreases G σ τ C hσ hdev
  have hsub : ∀ v, M τ v ⊆ M σ v := by
    intro v w hw
    have hw' : G.Adj v w ∧ τ w = τ v := (Finset.mem_filter.mp hw).2
    have heq : σ w = σ v := (step.1 v w hw'.1 hw'.2.symm).symm
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hw'.1, heq⟩
  have hτ : ∀ v, (M τ v).card ≤ 1 := by
    intro v
    exact le_trans (Finset.card_le_card (hsub v)) (hσ v)
  have hτA : τ ∈ A := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hτ⟩
  obtain ⟨v, w, hvw, hold, hnew⟩ := step.2
  have hmemold : w ∈ M σ v := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hvw, hold.symm⟩
  have hmemnew : w ∉ M τ v := by
    intro hw
    exact hnew ((Finset.mem_filter.mp hw).2.2.symm)
  have hstrict : M τ v ⊂ M σ v := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨hsub v, ?_⟩
    intro heq
    exact hmemnew (heq.symm ▸ hmemold)
  have hs : score τ < score σ := by
    dsimp [score]
    apply Finset.sum_lt_sum
    · intro i hi
      exact Finset.card_le_card (hsub i)
    · exact ⟨v, Finset.mem_univ _, Finset.card_lt_card hstrict⟩
  have hm := hmin τ hτA
  omega

#print axioms maxcut_defect_one_strong_deviation_mono_decreases
