import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsMaxcutOptimal
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongDeviation
import AFTD.Kb.GameTheoryEconomics.MaxcutUtilityAddMonochromaticCard
import AFTD.Kb.GameTheoryEconomics.MaxcutOptimalSameColorLe
import AFTD.Kb.GameTheoryEconomics.MaxcutWelfareSplit
import AFTD.Kb.GameTheoryEconomics.MaxcutUtility
import AFTD.Kb.GameTheoryEconomics.MaxcutUtilitySumSplit
import AFTD.Kb.GameTheoryEconomics.MaxcutWelfare

/-!
# maxcut_optimal_no_clique_deviation

Topic: equilibria   Node: 4af84e817228

Provenance: formalization of a published result. Source: arXiv:2610.04948

In the unweighted Max-k-Cut game on a finite simple graph, no coalition that induces a clique has a strong deviation from a welfare-optimal coloring.
-/

open scoped BigOperators

theorem maxcut_optimal_no_clique_deviation_mono_cancel {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (σ τ : V → Fin k)
    (hopt : is_maxcut_optimal G σ) (S : Finset V)
    (hagree : ∀ v ∉ S, τ v = σ v) (v : V)
    (hgain : maxcut_utility G σ v < maxcut_utility G τ v) :
    (S.filter fun w => G.Adj v w ∧ τ w = τ v).card <
      (S.filter fun w => G.Adj v w ∧ σ w = τ v).card := by
  have huσ := maxcut_utility_add_monochromatic_card G σ v
  have huτ := maxcut_utility_add_monochromatic_card G τ v
  have hopt_v := maxcut_optimal_same_color_le G σ hopt v (τ v)
  have hlt : (Finset.univ.filter fun w => G.Adj v w ∧ τ w = τ v).card <
      (Finset.univ.filter fun w => G.Adj v w ∧ σ w = τ v).card := by omega
  have h_split (p : V → Prop) [DecidablePred p] :
      (Finset.univ.filter p).card = (S.filter p).card + (Sᶜ.filter p).card := by
    simp only [Finset.card_filter]
    exact (Finset.sum_add_sum_compl S _).symm
  have h_split_τ := h_split (fun w => G.Adj v w ∧ τ w = τ v)
  have h_split_σ := h_split (fun w => G.Adj v w ∧ σ w = τ v)
  have h_compl_eq : (Sᶜ.filter fun w => G.Adj v w ∧ τ w = τ v).card =
      (Sᶜ.filter fun w => G.Adj v w ∧ σ w = τ v).card := by
    congr 1
    refine Finset.filter_congr fun w hw => ?_
    rw [Finset.mem_compl] at hw
    rw [hagree w hw]
  rw [h_split_τ, h_split_σ, h_compl_eq] at hlt
  omega

theorem maxcut_optimal_no_clique_deviation_clique_tau_fiber {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V) (hclique : G.IsClique (S : Set V))
    {k : ℕ} (τ : V → Fin k) (v : V) (hv : v ∈ S) :
    (S.filter fun w => τ w = τ v).card =
      (S.filter fun w => G.Adj v w ∧ τ w = τ v).card + 1 := by
  have h_eq : (S.filter fun w => τ w = τ v) =
      insert v (S.filter fun w => G.Adj v w ∧ τ w = τ v) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hw, hcol⟩
      rcases eq_or_ne w v with rfl | hne
      · left; rfl
      · right
        refine ⟨hw, ?_, hcol⟩
        exact G.adj_symm (hclique (Finset.mem_coe.2 hw) (Finset.mem_coe.2 hv) hne)
    · rintro (rfl | ⟨hw, _, hcol⟩)
      · exact ⟨hv, rfl⟩
      · exact ⟨hw, hcol⟩
  have hv_not_mem : v ∉ S.filter fun w => G.Adj v w ∧ τ w = τ v := by simp
  rw [h_eq, Finset.card_insert_of_notMem hv_not_mem]

theorem maxcut_optimal_no_clique_deviation_clique_sigma_fiber_le {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    {k : ℕ} (σ : V → Fin k) (v : V) (c : Fin k) :
    (S.filter fun w => G.Adj v w ∧ σ w = c).card ≤
      (S.filter fun w => σ w = c).card := by
  refine Finset.card_le_card fun w hw => ?_
  simp only [Finset.mem_filter] at hw ⊢
  exact ⟨hw.1, hw.2.2⟩

theorem maxcut_optimal_no_clique_deviation_fiber_eq_of_le_and_sum_eq {k : ℕ} (f g : Fin k → ℕ)
    (hle : ∀ c, f c ≤ g c) (hsum : ∑ c, f c = ∑ c, g c) (c : Fin k) :
    f c = g c := by
  by_contra hc
  have hlt : f c < g c := Nat.lt_of_le_of_ne (hle c) hc
  have : ∑ x, f x < ∑ x, g x :=
    Finset.sum_lt_sum (fun x _ => hle x) ⟨c, Finset.mem_univ c, hlt⟩
  omega

theorem maxcut_optimal_no_clique_deviation_A_clique_eq {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (hclique : G.IsClique (S : Set V)) {k : ℕ} (σ τ : V → Fin k)
    (hfiber : ∀ c : Fin k, (S.filter fun w => τ w = c).card = (S.filter fun w => σ w = c).card) :
    ∑ v ∈ S, ∑ w ∈ S, (if G.Adj v w ∧ τ w ≠ τ v then 1 else 0 : ℕ) =
      ∑ v ∈ S, ∑ w ∈ S, (if G.Adj v w ∧ σ w ≠ σ v then 1 else 0 : ℕ) := by
  have h_simp (ρ : V → Fin k) :
      ∑ v ∈ S, ∑ w ∈ S, (if G.Adj v w ∧ ρ w ≠ ρ v then 1 else 0 : ℕ) =
        ∑ c : Fin k, (S.filter fun v => ρ v = c).card * (S.card - (S.filter fun w => ρ w = c).card) := by
    have h1 : ∑ v ∈ S, ∑ w ∈ S, (if G.Adj v w ∧ ρ w ≠ ρ v then 1 else 0 : ℕ) =
        ∑ v ∈ S, ∑ w ∈ S, (if ρ w ≠ ρ v then 1 else 0 : ℕ) := by
      refine Finset.sum_congr rfl fun v hv => Finset.sum_congr rfl fun w hw => ?_
      rcases eq_or_ne w v with rfl | hne
      · simp
      · have : G.Adj v w := G.adj_symm (hclique (Finset.mem_coe.2 hw) (Finset.mem_coe.2 hv) hne)
        simp [this]
    rw [h1]
    have h2 : ∀ v ∈ S, ∑ w ∈ S, (if ρ w ≠ ρ v then 1 else 0 : ℕ) =
        S.card - (S.filter fun w => ρ w = ρ v).card := by
      intro v _
      rw [← Finset.card_filter]
      have hnot := Finset.card_filter_add_card_filter_not (s := S) (p := fun w => ρ w = ρ v)
      change (S.filter fun w => ρ w = ρ v).card + (S.filter fun w => ρ w ≠ ρ v).card = S.card at hnot
      omega
    have h3 : ∑ v ∈ S, ∑ w ∈ S, (if ρ w ≠ ρ v then 1 else 0 : ℕ) =
        ∑ v ∈ S, (fun v => S.card - (S.filter fun w => ρ w = ρ v).card) v := by
      exact Finset.sum_congr rfl h2
    rw [h3]
    have h4 := Finset.sum_fiberwise_of_maps_to (g := ρ) (s := S) (t := Finset.univ)
      (fun _ _ => Finset.mem_univ _) (fun v => S.card - (S.filter fun w => ρ w = ρ v).card)
    rw [← h4]
    refine Finset.sum_congr rfl fun c _ => ?_
    have hconst : ∀ v ∈ S.filter fun v => ρ v = c,
        (S.card - (S.filter fun w => ρ w = ρ v).card) =
        (S.card - (S.filter fun w => ρ w = c).card) := by
      intro v hv
      simp only [Finset.mem_filter] at hv
      rw [hv.2]
    rw [Finset.sum_congr rfl hconst, Finset.sum_const, smul_eq_mul]
  rw [h_simp τ, h_simp σ]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [hfiber c]

/-- Every welfare-optimal coloring in the Max-k-Cut game resists strong deviations by clique coalitions. -/
theorem maxcut_optimal_no_clique_deviation {V : Type} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (σ : V → Fin k)
    (hopt : is_maxcut_optimal G σ) (S : Finset V) (hclique : G.IsClique (S : Set V))
    (τ : V → Fin k) : ¬ is_maxcut_strong_deviation G σ S τ := by
  classical
  intro hdev
  obtain ⟨hne, hagree, hgain⟩ := hdev
  have hle : ∀ c : Fin k, (S.filter fun w => τ w = c).card ≤ (S.filter fun w => σ w = c).card := by
    intro c
    rcases (S.filter fun w => τ w = c).eq_empty_or_nonempty with he | ⟨v, hv⟩
    · rw [he, Finset.card_empty]; omega
    · simp only [Finset.mem_filter] at hv
      have h1 := maxcut_optimal_no_clique_deviation_mono_cancel G σ τ hopt S hagree v (hgain v hv.1)
      have h2 := maxcut_optimal_no_clique_deviation_clique_tau_fiber G S hclique τ v hv.1
      have h3 := maxcut_optimal_no_clique_deviation_clique_sigma_fiber_le G S σ v (τ v)
      rw [hv.2] at h1 h2 h3
      omega
  have hsum_τ : ∑ c : Fin k, (S.filter fun w => τ w = c).card = S.card := by
    have := Finset.card_eq_sum_card_fiberwise (s := S) (t := Finset.univ) (f := τ)
      (fun _ _ => Finset.mem_univ _)
    rw [← this]
  have hsum_σ : ∑ c : Fin k, (S.filter fun w => σ w = c).card = S.card := by
    have := Finset.card_eq_sum_card_fiberwise (s := S) (t := Finset.univ) (f := σ)
      (fun _ _ => Finset.mem_univ _)
    rw [← this]
  have hsum_eq : ∑ c : Fin k, (S.filter fun w => τ w = c).card =
      ∑ c : Fin k, (S.filter fun w => σ w = c).card := by
    rw [hsum_τ, hsum_σ]
  have hfiber : ∀ c : Fin k, (S.filter fun w => τ w = c).card = (S.filter fun w => σ w = c).card :=
    fun c => maxcut_optimal_no_clique_deviation_fiber_eq_of_le_and_sum_eq _ _ hle hsum_eq c
  have hA_eq := maxcut_optimal_no_clique_deviation_A_clique_eq G S hclique σ τ hfiber
  have hS := maxcut_welfare_split G σ S
  have hT := maxcut_welfare_split G τ S
  have hC : ∑ x ∈ Sᶜ, ∑ w ∈ Sᶜ, (if G.Adj x w ∧ τ w ≠ τ x then 1 else 0 : ℕ) =
      ∑ x ∈ Sᶜ, ∑ w ∈ Sᶜ, (if G.Adj x w ∧ σ w ≠ σ x then 1 else 0 : ℕ) := by
    refine Finset.sum_congr rfl fun x hx => Finset.sum_congr rfl fun w hw => ?_
    rw [hagree x (Finset.mem_compl.1 hx), hagree w (Finset.mem_compl.1 hw)]
  have hUS := maxcut_utility_sum_split G σ S
  have hUT := maxcut_utility_sum_split G τ S
  have hgains : ∑ v ∈ S, maxcut_utility G σ v + S.card ≤ ∑ v ∈ S, maxcut_utility G τ v := by
    have := Finset.sum_le_sum fun v hv => Nat.succ_le_of_lt (hgain v hv)
    simpa [Finset.sum_add_distrib] using this
  have hcard : 1 ≤ S.card := Finset.card_pos.2 hne
  have hopt' := hopt τ
  omega
