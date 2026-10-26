import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutDeviationMonoInsideDrop
import AFTD.Kb.GameTheoryEconomics.IsMaxcutOptimal
import AFTD.Kb.GameTheoryEconomics.MaxcutUtility
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongDeviation
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongEquilibrium

/-!
# maxcut_optimal_strong_of_internal_mono_lt

Topic: equilibria   Node: 1879b67ef394

Provenance: helper lemma. step towards maxcut_op89_optimal_strong_equilibrium_exists

If σ is an optimal colouring of the unweighted Max-k-Cut game on a finite simple graph G and every nonempty set S of vertices carries fewer than 2|S| ordered monochromatic adjacent pairs under σ (that is Σ_{v∈S} Σ_{w∈S} [v adjacent w and σ(w) = σ(v)] < 2|S|), then σ is a strong equilibrium.
-/

/-- An optimal colouring whose every nonempty vertex set carries fewer than 2|S| ordered monochromatic internal pairs is a strong equilibrium. -/
theorem maxcut_optimal_strong_of_internal_mono_lt {V : Type} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (σ : V → Fin k)
    (hopt : is_maxcut_optimal G σ)
    (hS : ∀ S : Finset V, S.Nonempty →
      (∑ v ∈ S, ∑ w ∈ S, (if G.Adj v w ∧ σ w = σ v then 1 else 0 : ℕ)) < 2 * S.card) :
    is_maxcut_strong_equilibrium G σ := by
  classical
  intro S τ hdev
  have hdrop := maxcut_deviation_mono_inside_drop G σ τ S hopt hdev
  have hlt := hS S hdev.1
  have hnonneg : (0:ℕ) ≤ ∑ v ∈ S, ∑ w ∈ S, (if G.Adj v w ∧ τ w = τ v then 1 else 0 : ℕ) :=
    Nat.zero_le _
  omega
