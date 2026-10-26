import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutOptimalSameColorLe
import AFTD.Kb.GameTheoryEconomics.MaxcutUtilityAddMonochromaticCard
import AFTD.Kb.GameTheoryEconomics.MaxcutUtilityLeDegree
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongEquilibrium
import AFTD.Kb.GameTheoryEconomics.MaxcutUtility
import AFTD.Kb.GameTheoryEconomics.IsMaxcutOptimal
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongDeviation

/-!
# maxcut_optimal_strong_of_color_unused

Topic: equilibria   Node: 98b5f087910a

Provenance: helper lemma. step towards maxcut_op89_optimal_strong_equilibrium_exists

If σ is an optimal colouring of the unweighted Max-k-Cut game on a finite simple graph G and some colour c is never used by σ, then σ is a strong equilibrium.
-/

/-- An optimal colouring that leaves a colour unused is automatically a strong equilibrium. -/
theorem maxcut_optimal_strong_of_color_unused {V : Type} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (hk : 0 < k) (σ : V → Fin k)
    (c : Fin k) (hc : ∀ v, σ v ≠ c) (hopt : is_maxcut_optimal G σ) :
    is_maxcut_strong_equilibrium G σ := by
  intro S τ hdev
  rcases hdev with ⟨hne, -, hstrict⟩
  obtain ⟨v, hv⟩ := hne
  have h_c_empty : (Finset.univ.filter fun w => G.Adj v w ∧ σ w = c) = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro w _ hw
    exact hc w hw.2
  have h_same_le := maxcut_optimal_same_color_le G σ hopt v c
  rw [h_c_empty, Finset.card_empty] at h_same_le
  have h_add := maxcut_utility_add_monochromatic_card G σ v
  have h_tau_le := maxcut_utility_le_degree G τ v
  have hlt := hstrict v hv
  omega
