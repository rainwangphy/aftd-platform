import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutUtilityColorPermutation
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongEquilibrium
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongDeviation
import AFTD.Kb.GameTheoryEconomics.MaxcutUtility

/-!
# maxcut_strong_equilibrium_color_permutation

Topic: equilibria   Node: 33317863d788

Provenance: helper lemma. Structural reduction for OP-85, the strong-equilibrium existence problem; the two-piece gluing step is maxcut_single_vertex_sum_strong_equilibrium.

A global permutation of colors maps a strong equilibrium to a strong equilibrium.
-/

theorem maxcut_strong_equilibrium_color_permutation {V : Type} [Fintype V] (G : SimpleGraph V)
    [DecidableRel G.Adj] {k : ℕ} (σ : V → Fin k) (p : Equiv.Perm (Fin k))
    (h : is_maxcut_strong_equilibrium G σ) :
    is_maxcut_strong_equilibrium G (fun v => p (σ v)) := by
  intro S τ hd
  apply h S (fun v => p.symm (τ v))
  refine ⟨hd.1, ?_, ?_⟩
  · intro v hv
    change p.symm (τ v) = σ v
    rw [hd.2.1 v hv]
    exact p.symm_apply_apply (σ v)
  · intro v hv
    have hg := hd.2.2 v hv
    rw [maxcut_utility_color_permutation G σ p v] at hg
    have heq := maxcut_utility_color_permutation G (fun v => p.symm (τ v)) p v
    simp only [Equiv.apply_symm_apply] at heq
    rw [← heq]
    exact hg
