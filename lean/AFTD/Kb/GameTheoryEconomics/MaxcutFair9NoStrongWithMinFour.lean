import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutFair9Graph
import AFTD.Kb.GameTheoryEconomics.MaxcutFair9Colors
import AFTD.Kb.GameTheoryEconomics.MaxcutFair9Targets
import AFTD.Kb.GameTheoryEconomics.MaxcutFair9Deviation
import AFTD.Kb.GameTheoryEconomics.MaxcutFair9NormalizedCertificates
import AFTD.Kb.GameTheoryEconomics.MaxcutStrongEquilibriumColorPermutation
import AFTD.Kb.GameTheoryEconomics.MaxcutUtilityColorPermutation
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongDeviation
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongEquilibrium
import AFTD.Kb.GameTheoryEconomics.MaxcutUtility

/-!
# maxcut_fair9_no_strong_with_min_four

Topic: equilibria   Node: dfd2aa60e355

Provenance: helper lemma. Nine-vertex finite obstruction to fair Nash selection in the OP-85 strong-equilibrium campaign, discovered in experiment 12959 and independently checked in 12961, 12964, and 12973.

No strong equilibrium of the nine-vertex graph with three colors gives every vertex utility at least four.
-/

set_option maxRecDepth 200000
set_option maxHeartbeats 0
set_option synthInstance.maxSize 200000
private instance : DecidableRel maxcut_fair9_graph.Adj := by
  unfold maxcut_fair9_graph SimpleGraph.fromRel
  infer_instance
private instance (σ τ : Fin 9 → Fin 3) (S : Finset (Fin 9)) :
    Decidable (is_maxcut_strong_deviation maxcut_fair9_graph σ S τ) := by
  unfold is_maxcut_strong_deviation maxcut_utility
  infer_instance

private instance (σ τ : Fin 9 → Fin 3) : Decidable (maxcut_fair9_deviation σ τ) := by
  unfold maxcut_fair9_deviation is_maxcut_strong_deviation maxcut_utility
  infer_instance

theorem maxcut_fair9_no_strong_with_min_four : ∀ σ : Fin 9 → Fin 3,
    (∀ v : Fin 9, 4 ≤ maxcut_utility maxcut_fair9_graph σ v) →
    ¬ is_maxcut_strong_equilibrium maxcut_fair9_graph σ := by
  intro σ hmin hstable
  let p : Equiv.Perm (Fin 3) := Equiv.swap (σ 0) 0
  let ρ : Fin 9 → Fin 3 := fun v => p (σ v)
  have h0 : ρ 0 = 0 := by simp [ρ, p]
  have hρstable : is_maxcut_strong_equilibrium maxcut_fair9_graph ρ :=
    maxcut_strong_equilibrium_color_permutation maxcut_fair9_graph σ p hstable
  have hρmin : ∀ v, 4 ≤ maxcut_utility maxcut_fair9_graph ρ v := by
    intro v
    simpa [ρ, maxcut_utility_color_permutation] using hmin v
  have hρnash : ∀ v q, ¬ is_maxcut_strong_deviation maxcut_fair9_graph ρ {v} (Function.update ρ v q) := by
    intro v q
    exact hρstable {v} (Function.update ρ v q)
  have hvec : ρ = maxcut_fair9_colors (ρ 1) (ρ 2) (ρ 3) (ρ 4) (ρ 5) (ρ 6) (ρ 7) (ρ 8) := by
    funext v
    fin_cases v <;> simp [maxcut_fair9_colors, h0]
  have hc := maxcut_fair9_normalized_certificates (ρ 1) (ρ 2) (ρ 3) (ρ 4) (ρ 5) (ρ 6) (ρ 7) (ρ 8)
  rw [← hvec] at hc
  have ht := hc hρmin hρnash
  obtain ⟨τ, _, hτ⟩ := List.any_eq_true.mp ht
  have hdev : maxcut_fair9_deviation ρ τ := of_decide_eq_true hτ
  exact hρstable _ τ hdev
