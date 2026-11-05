import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongDeviation
import AFTD.Kb.GameTheoryEconomics.MaxcutUtilityAddMonochromaticCard
import AFTD.Kb.GameTheoryEconomics.MaxcutUtility

/-!
# maxcut_defect_one_strong_deviation_mono_decreases

Topic: equilibria   Node: 827f5fc477d0

Provenance: helper lemma. Unweighted Max-k-Cut definitions from arXiv:2610.04948, Section 1; elementary monochromatic-edge exchange.

A strong deviation from a coloring with at most one same-colored neighbor per vertex cannot create a monochromatic edge and must remove at least one.
-/

theorem maxcut_defect_one_strong_deviation_mono_decreases
    {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ}
    (σ τ : V → Fin k) (C : Finset V)
    (hdefect : ∀ v : V, (Finset.univ.filter fun w => G.Adj v w ∧ σ w = σ v).card ≤ 1)
    (hdev : is_maxcut_strong_deviation G σ C τ) :
    (∀ v w : V, G.Adj v w → τ v = τ w → σ v = σ w) ∧
    ∃ v w : V, G.Adj v w ∧ σ v = σ w ∧ τ v ≠ τ w := by
  classical
  have hz : ∀ v ∈ C, (Finset.univ.filter fun w => G.Adj v w ∧ τ w = τ v).card = 0 := by
    intro v hv
    have h₁ := maxcut_utility_add_monochromatic_card G σ v
    have h₂ := maxcut_utility_add_monochromatic_card G τ v
    have hg := hdev.2.2 v hv
    have hd := hdefect v
    omega
  have hz' : ∀ v ∈ C, ∀ w, G.Adj v w → τ w ≠ τ v := by
    intro v hv w hadj heq
    have hpos : 0 < (Finset.univ.filter fun z => G.Adj v z ∧ τ z = τ v).card := by
      apply Finset.card_pos.mpr
      exact ⟨w, Finset.mem_filter.mpr ⟨Finset.mem_univ w, hadj, heq⟩⟩
    have hh := hz v hv
    omega
  constructor
  · intro v w hadj heq
    by_cases hv : v ∈ C
    · exact (hz' v hv w hadj heq.symm).elim
    by_cases hw : w ∈ C
    · exact (hz' w hw v (hadj.symm) heq).elim
    calc
      σ v = τ v := (hdev.2.1 v hv).symm
      _ = τ w := heq
      _ = σ w := hdev.2.1 w hw
  · obtain ⟨v, hv⟩ := hdev.1
    have h₁ := maxcut_utility_add_monochromatic_card G σ v
    have h₂ := maxcut_utility_add_monochromatic_card G τ v
    have hg := hdev.2.2 v hv
    have hpos : 0 < (Finset.univ.filter fun w => G.Adj v w ∧ σ w = σ v).card := by omega
    obtain ⟨w, hw⟩ := Finset.card_pos.mp hpos
    have hw' := Finset.mem_filter.mp hw
    refine ⟨v, w, hw'.2.1, hw'.2.2.symm, ?_⟩
    exact Ne.symm (hz' v hv w hw'.2.1)
