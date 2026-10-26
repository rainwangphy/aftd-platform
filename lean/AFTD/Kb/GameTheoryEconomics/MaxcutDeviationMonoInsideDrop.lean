import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutUtilitySumSplit
import AFTD.Kb.GameTheoryEconomics.MaxcutWelfareSplit
import AFTD.Kb.GameTheoryEconomics.MaxcutUtility
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongDeviation
import AFTD.Kb.GameTheoryEconomics.MaxcutWelfare
import AFTD.Kb.GameTheoryEconomics.IsMaxcutOptimal

/-!
# maxcut_deviation_mono_inside_drop

Topic: equilibria   Node: 621491e1c4b0

Provenance: helper lemma. step towards maxcut_op89_optimal_strong_equilibrium_exists

Let σ be an optimal colouring of the unweighted Max-k-Cut game on a finite simple graph G and let (S,τ) be a strong deviation from σ. Then the number of ordered monochromatic adjacent pairs inside S drops by at least 2|S|: with M(ρ) = Σ_{v∈S} Σ_{w∈S} [v adjacent w and ρ(w) = ρ(v)], one has M(τ) + 2|S| ≤ M(σ). Halving, this is arXiv:2610.04948, Theorem 8: a deviating coalition from an optimal colouring removes at least |S| monochromatic edges inside itself.
-/

/-- A strong deviation from an optimal colouring destroys at least 2|S| ordered monochromatic pairs inside the coalition. -/
theorem maxcut_deviation_mono_inside_drop {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (σ τ : V → Fin k) (S : Finset V)
    (hopt : is_maxcut_optimal G σ) (hdev : is_maxcut_strong_deviation G σ S τ) :
    (∑ v ∈ S, ∑ w ∈ S, (if G.Adj v w ∧ τ w = τ v then 1 else 0 : ℕ)) + 2 * S.card ≤
      ∑ v ∈ S, ∑ w ∈ S, (if G.Adj v w ∧ σ w = σ v then 1 else 0 : ℕ) := by
  obtain ⟨hne, hout, hgain⟩ := hdev
  have hgains : ∑ v ∈ S, maxcut_utility G σ v + S.card ≤
      ∑ v ∈ S, maxcut_utility G τ v := by
    have := Finset.sum_le_sum fun v hv => Nat.succ_le_of_lt (hgain v hv)
    simpa [Finset.sum_add_distrib] using this
  have hu_σ := maxcut_utility_sum_split G σ S
  have hu_τ := maxcut_utility_sum_split G τ S
  have hw_σ := maxcut_welfare_split G σ S
  have hw_τ := maxcut_welfare_split G τ S
  have hop := hopt τ
  have hC : (∑ v ∈ Sᶜ, ∑ w ∈ Sᶜ, (if G.Adj v w ∧ τ w ≠ τ v then 1 else 0 : ℕ)) =
      ∑ v ∈ Sᶜ, ∑ w ∈ Sᶜ, (if G.Adj v w ∧ σ w ≠ σ v then 1 else 0 : ℕ) := by
    refine Finset.sum_congr rfl fun v hv => Finset.sum_congr rfl fun w hw => ?_
    rw [Finset.mem_compl] at hv hw
    rw [hout v hv, hout w hw]
  have hM (ρ : V → Fin k) :
      (∑ v ∈ S, ∑ w ∈ S, (if G.Adj v w ∧ ρ w = ρ v then 1 else 0 : ℕ)) +
        (∑ v ∈ S, ∑ w ∈ S, (if G.Adj v w ∧ ρ w ≠ ρ v then 1 else 0 : ℕ)) =
        ∑ v ∈ S, ∑ w ∈ S, (if G.Adj v w then 1 else 0 : ℕ) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun v hv => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun w hw => ?_
    by_cases h : G.Adj v w
    · by_cases heq : ρ w = ρ v
      · simp [h, heq]
      · simp [h, heq]
    · simp [h]
  have hM_σ := hM σ
  have hM_τ := hM τ
  omega
