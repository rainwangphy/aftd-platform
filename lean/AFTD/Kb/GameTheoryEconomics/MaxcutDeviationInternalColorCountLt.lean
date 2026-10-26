import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutOptimalSameColorLe
import AFTD.Kb.GameTheoryEconomics.MaxcutUtilityAddMonochromaticCard
import AFTD.Kb.GameTheoryEconomics.MaxcutUtility
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongDeviation
import AFTD.Kb.GameTheoryEconomics.IsMaxcutOptimal

/-!
# maxcut_deviation_internal_color_count_lt

Topic: equilibria   Node: e5ac750fd3f8

Provenance: helper lemma. step towards maxcut_op89_optimal_strong_equilibrium_exists

Let σ be an optimal colouring of the unweighted Max-k-Cut game on a finite simple graph G and let (S,τ) be a strong deviation from σ. Then every member v of the coalition ends up with strictly fewer coalition-neighbours of the colour it moves to than it had of that colour before: #{w ∈ S : v adjacent w and τ(w) = τ(v)} < #{w ∈ S : v adjacent w and σ(w) = τ(v)}.
-/

/-- Each deviating player at an optimal colouring strictly reduces its count of coalition-neighbours of the colour it switches to. -/
theorem maxcut_deviation_internal_color_count_lt {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (σ τ : V → Fin k) (S : Finset V)
    (hopt : is_maxcut_optimal G σ) (hdev : is_maxcut_strong_deviation G σ S τ)
    {v : V} (hv : v ∈ S) :
    (S.filter fun w => G.Adj v w ∧ τ w = τ v).card <
      (S.filter fun w => G.Adj v w ∧ σ w = τ v).card := by
  have hu : maxcut_utility G σ v < maxcut_utility G τ v := hdev.2.2 v hv
  have hσ_deg := maxcut_utility_add_monochromatic_card G σ v
  have hτ_deg := maxcut_utility_add_monochromatic_card G τ v
  have h1 : (Finset.univ.filter fun w => G.Adj v w ∧ τ w = τ v).card <
      (Finset.univ.filter fun w => G.Adj v w ∧ σ w = σ v).card := by
    omega
  have h2 : (Finset.univ.filter fun w => G.Adj v w ∧ σ w = σ v).card ≤
      (Finset.univ.filter fun w => G.Adj v w ∧ σ w = τ v).card :=
    maxcut_optimal_same_color_le G σ hopt v (τ v)
  have hlt : (Finset.univ.filter fun w => G.Adj v w ∧ τ w = τ v).card <
      (Finset.univ.filter fun w => G.Adj v w ∧ σ w = τ v).card :=
    lt_of_lt_of_le h1 h2

  have hsplit_τ : (Finset.filter (· ∈ S) (Finset.univ.filter (fun w => G.Adj v w ∧ τ w = τ v))).card +
      (Finset.filter (· ∉ S) (Finset.univ.filter (fun w => G.Adj v w ∧ τ w = τ v))).card =
      (Finset.univ.filter (fun w => G.Adj v w ∧ τ w = τ v)).card :=
    Finset.card_filter_add_card_filter_not (s := Finset.univ.filter (fun w => G.Adj v w ∧ τ w = τ v)) (· ∈ S)
  have hsplit_σ : (Finset.filter (· ∈ S) (Finset.univ.filter (fun w => G.Adj v w ∧ σ w = τ v))).card +
      (Finset.filter (· ∉ S) (Finset.univ.filter (fun w => G.Adj v w ∧ σ w = τ v))).card =
      (Finset.univ.filter (fun w => G.Adj v w ∧ σ w = τ v)).card :=
    Finset.card_filter_add_card_filter_not (s := Finset.univ.filter (fun w => G.Adj v w ∧ σ w = τ v)) (· ∈ S)

  have hS_τ : Finset.filter (· ∈ S) (Finset.univ.filter (fun w => G.Adj v w ∧ τ w = τ v)) =
      Finset.filter (fun w => G.Adj v w ∧ τ w = τ v) S := by
    ext w; simp [and_comm]
  have hS_σ : Finset.filter (· ∈ S) (Finset.univ.filter (fun w => G.Adj v w ∧ σ w = τ v)) =
      Finset.filter (fun w => G.Adj v w ∧ σ w = τ v) S := by
    ext w; simp [and_comm]

  have h_out : Finset.filter (· ∉ S) (Finset.univ.filter (fun w => G.Adj v w ∧ τ w = τ v)) =
      Finset.filter (· ∉ S) (Finset.univ.filter (fun w => G.Adj v w ∧ σ w = τ v)) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨hadj, hτ_w⟩, hw⟩
      rw [hdev.2.1 w hw] at hτ_w
      exact ⟨⟨hadj, hτ_w⟩, hw⟩
    · rintro ⟨⟨hadj, hσ_w⟩, hw⟩
      rw [← hdev.2.1 w hw] at hσ_w
      exact ⟨⟨hadj, hσ_w⟩, hw⟩

  rw [hS_τ] at hsplit_τ
  rw [hS_σ] at hsplit_σ
  rw [h_out] at hsplit_τ
  omega
