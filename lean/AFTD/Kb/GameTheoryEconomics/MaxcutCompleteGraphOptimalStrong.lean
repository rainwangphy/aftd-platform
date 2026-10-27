import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutCompleteGraphOptimalBalanced
import AFTD.Kb.GameTheoryEconomics.IsMaxcutOptimal
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongDeviation
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongEquilibrium
import AFTD.Kb.GameTheoryEconomics.MaxcutUtility

/-!
# maxcut_complete_graph_optimal_strong

Topic: equilibria   Node: 56bf691ea584

Provenance: helper lemma. step towards maxcut_op89_optimal_strong_equilibrium_exists

Every optimal k-colouring of the complete graph K_n is a strong equilibrium of the Max-k-Cut game, so no coalition can strictly raise all of its members' utilities. Consequently K_n admits an optimal strong equilibrium for every k and every n, an infinite family inside the residual case of OP-89: χ(K_n) = n > k, and neither the bound n ≤ 2k+1 nor Δ ≤ 2k-1 applies.
-/

private def maxcut_complete_graph_optimal_strong_cls {n k : ℕ} (ρ : Fin n → Fin k) (c : Fin k) : ℕ :=
  (Finset.univ.filter fun v => ρ v = c).card

private def maxcut_complete_graph_optimal_strong_clsS {n k : ℕ} (ρ : Fin n → Fin k) (S : Finset (Fin n)) (c : Fin k) : ℕ :=
  (S.filter fun v => ρ v = c).card

private lemma maxcut_complete_graph_optimal_strong_cls_sum {n k : ℕ} (ρ : Fin n → Fin k) :
    ∑ c : Fin k, maxcut_complete_graph_optimal_strong_cls ρ c = n := by
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Finset (Fin n))) (f := ρ) (t := (Finset.univ : Finset (Fin k)))
    (fun v _ => Finset.mem_univ (ρ v))
  rw [Finset.card_univ, Fintype.card_fin] at h
  exact h.symm

private lemma maxcut_complete_graph_optimal_strong_util_top {n k : ℕ} (ρ : Fin n → Fin k) (v : Fin n) :
    maxcut_utility (⊤ : SimpleGraph (Fin n)) ρ v
      = n - maxcut_complete_graph_optimal_strong_cls ρ (ρ v) := by
  have h1 : (Finset.univ.filter fun w => (⊤ : SimpleGraph (Fin n)).Adj v w ∧ ρ w ≠ ρ v)
      = (Finset.univ.filter fun w => ρ w ≠ ρ v) := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, SimpleGraph.top_adj]
    constructor
    · exact fun h => h.2
    · intro h
      exact ⟨fun hvw => h (congrArg ρ hvw.symm), h⟩
  have h2 : (Finset.univ.filter fun w => ρ w ≠ ρ v)
      = ((Finset.univ.filter fun w => ρ w = ρ v))ᶜ := by
    ext w; simp
  rw [maxcut_utility, h1, h2, Finset.card_compl, Fintype.card_fin]
  rfl

private lemma maxcut_complete_graph_optimal_strong_cls_split {n k : ℕ} (σ τ : Fin n → Fin k)
    (S : Finset (Fin n)) (hfix : ∀ v, v ∉ S → τ v = σ v) (c : Fin k) :
    maxcut_complete_graph_optimal_strong_cls σ c + maxcut_complete_graph_optimal_strong_clsS τ S c
      = maxcut_complete_graph_optimal_strong_cls τ c + maxcut_complete_graph_optimal_strong_clsS σ S c := by
  have hEA : S.filter (fun v : Fin n => σ v = c)
      = (Finset.univ.filter (fun v : Fin n => σ v = c)).filter (fun v => v ∈ S) := by
    ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; tauto
  have hXA : (Finset.univ.filter (fun v : Fin n => σ v = c)).filter (fun v => v ∉ S)
      = (Sᶜ).filter (fun v => σ v = c) := by
    ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl]; tauto
  have hDB : S.filter (fun v : Fin n => τ v = c)
      = (Finset.univ.filter (fun v : Fin n => τ v = c)).filter (fun v => v ∈ S) := by
    ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; tauto
  have hYB : (Finset.univ.filter (fun v : Fin n => τ v = c)).filter (fun v => v ∉ S)
      = (Sᶜ).filter (fun v => τ v = c) := by
    ext v; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl]; tauto
  have hXY : (Sᶜ).filter (fun v => σ v = c) = (Sᶜ).filter (fun v => τ v = c) := by
    apply Finset.filter_congr
    intro v hv
    simp only [Finset.mem_compl] at hv
    rw [hfix v hv]
  have hAcard := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun v : Fin n => σ v = c)) (p := fun v => v ∈ S)
  have hBcard := Finset.card_filter_add_card_filter_not
    (s := Finset.univ.filter (fun v : Fin n => τ v = c)) (p := fun v => v ∈ S)
  rw [← hEA, hXA, hXY] at hAcard
  rw [← hDB, hYB] at hBcard
  simp only [maxcut_complete_graph_optimal_strong_cls, maxcut_complete_graph_optimal_strong_clsS]
  omega

private lemma maxcut_complete_graph_optimal_strong_cls_le {n k : ℕ} (ρ : Fin n → Fin k) (c : Fin k) :
    maxcut_complete_graph_optimal_strong_cls ρ c ≤ n := by
  have := Finset.card_le_univ (Finset.univ.filter fun v => ρ v = c)
  simpa [maxcut_complete_graph_optimal_strong_cls, Fintype.card_fin] using this

/-- Every optimal colouring of the complete graph K_n is a strong equilibrium; K_n is an unbounded family lying strictly inside the residual (χ > k, n ≥ 2k+2, Δ ≥ 2k) regime of OP-89. -/
theorem maxcut_complete_graph_optimal_strong {n k : ℕ} (σ : Fin n → Fin k) (hopt : is_maxcut_optimal (⊤ : SimpleGraph (Fin n)) σ) : is_maxcut_strong_equilibrium (⊤ : SimpleGraph (Fin n)) σ := by
  intro S τ hdev
  obtain ⟨hSne, hfix, himp⟩ := hdev
  rcases Nat.eq_zero_or_pos k with hk | hk
  · obtain ⟨v, hv⟩ := hSne
    exact Fin.elim0 (hk ▸ τ v)
  have huniv : (Finset.univ : Finset (Fin k)).Nonempty := ⟨⟨0, hk⟩, Finset.mem_univ _⟩
  obtain ⟨c0, -, hmin⟩ := Finset.exists_min_image (Finset.univ : Finset (Fin k))
    (fun c => maxcut_complete_graph_optimal_strong_cls σ c) huniv
  let q : ℕ := maxcut_complete_graph_optimal_strong_cls σ c0
  have hq_le : ∀ c : Fin k, q ≤ maxcut_complete_graph_optimal_strong_cls σ c :=
    fun c => hmin c (Finset.mem_univ c)
  have hA_le : ∀ c : Fin k, maxcut_complete_graph_optimal_strong_cls σ c ≤ q + 1 := by
    intro c
    have hb := maxcut_complete_graph_optimal_balanced σ hopt c c0
    simpa [maxcut_complete_graph_optimal_strong_cls, q] using hb
  have hstep1 : ∀ v ∈ S, maxcut_complete_graph_optimal_strong_cls τ (τ v)
      < maxcut_complete_graph_optimal_strong_cls σ (σ v) := by
    intro v hv
    have h := himp v hv
    rw [maxcut_complete_graph_optimal_strong_util_top σ v,
        maxcut_complete_graph_optimal_strong_util_top τ v] at h
    have hA := maxcut_complete_graph_optimal_strong_cls_le σ (σ v)
    have hB := maxcut_complete_graph_optimal_strong_cls_le τ (τ v)
    omega
  have hB_le : ∀ c : Fin k, maxcut_complete_graph_optimal_strong_cls τ c ≤ q + 1 := by
    intro c
    by_cases hD : maxcut_complete_graph_optimal_strong_clsS τ S c = 0
    · have hsp := maxcut_complete_graph_optimal_strong_cls_split σ τ S hfix c
      rw [hD, add_zero] at hsp
      have hAl := hA_le c
      omega
    · have hne : (S.filter fun v => τ v = c).Nonempty := Finset.card_ne_zero.mp hD
      obtain ⟨v, hv⟩ := hne
      rw [Finset.mem_filter] at hv
      obtain ⟨hvS, hvc⟩ := hv
      have h1 := hstep1 v hvS
      have h2 := hA_le (σ v)
      have h3 : maxcut_complete_graph_optimal_strong_cls τ c
          = maxcut_complete_graph_optimal_strong_cls τ (τ v) := by rw [← hvc]
      omega
  have hD_of_B : ∀ c : Fin k, maxcut_complete_graph_optimal_strong_cls τ c = q + 1 →
      maxcut_complete_graph_optimal_strong_clsS τ S c = 0 := by
    intro c hc
    by_contra hDnz
    have hne : (S.filter fun v => τ v = c).Nonempty := Finset.card_ne_zero.mp hDnz
    obtain ⟨v, hv⟩ := hne
    rw [Finset.mem_filter] at hv
    obtain ⟨hvS, hvc⟩ := hv
    have h1 := hstep1 v hvS
    have h2 := hA_le (σ v)
    rw [hvc] at h1
    omega
  have hAB : ∀ c : Fin k, maxcut_complete_graph_optimal_strong_cls τ c = q + 1 →
      maxcut_complete_graph_optimal_strong_cls σ c = q + 1 := by
    intro c hc
    have hD := hD_of_B c hc
    have hsp := maxcut_complete_graph_optimal_strong_cls_split σ τ S hfix c
    rw [hD, add_zero] at hsp
    have hAl := hA_le c
    omega
  have hEq_of_B : ∀ c : Fin k, maxcut_complete_graph_optimal_strong_cls τ c = q + 1 →
      maxcut_complete_graph_optimal_strong_clsS σ S c = 0 := by
    intro c hc
    have hD := hD_of_B c hc
    have hAq := hAB c hc
    have hsp := maxcut_complete_graph_optimal_strong_cls_split σ τ S hfix c
    rw [hD, add_zero, hAq, hc] at hsp
    omega
  have hsumA := maxcut_complete_graph_optimal_strong_cls_sum σ
  have hsumB := maxcut_complete_graph_optimal_strong_cls_sum τ
  let uA : ℕ := (Finset.univ.filter fun c : Fin k => maxcut_complete_graph_optimal_strong_cls σ c = q + 1).card
  let uB : ℕ := (Finset.univ.filter fun c : Fin k => maxcut_complete_graph_optimal_strong_cls τ c = q + 1).card
  have hA_eq : ∀ c : Fin k, maxcut_complete_graph_optimal_strong_cls σ c
      = q + (if maxcut_complete_graph_optimal_strong_cls σ c = q + 1 then 1 else 0) := by
    intro c
    have h1 := hq_le c; have h2 := hA_le c
    split_ifs with hh <;> omega
  have hsumA_eq : ∑ c : Fin k, maxcut_complete_graph_optimal_strong_cls σ c = k * q + uA := by
    have hcongr : ∑ c : Fin k, maxcut_complete_graph_optimal_strong_cls σ c
        = ∑ c : Fin k, (q + (if maxcut_complete_graph_optimal_strong_cls σ c = q + 1 then 1 else 0)) :=
      Finset.sum_congr rfl (fun c _ => hA_eq c)
    rw [hcongr, Finset.sum_add_distrib, Finset.sum_const, ← Finset.card_filter]
    simp [uA, Finset.card_univ, Fintype.card_fin]
  have hB_bound : ∀ c : Fin k, maxcut_complete_graph_optimal_strong_cls τ c
      ≤ q + (if maxcut_complete_graph_optimal_strong_cls τ c = q + 1 then 1 else 0) := by
    intro c
    have h := hB_le c
    split_ifs with hh <;> omega
  have hBsum_aux : ∑ c : Fin k,
      (q + (if maxcut_complete_graph_optimal_strong_cls τ c = q + 1 then 1 else 0)) = k * q + uB := by
    rw [Finset.sum_add_distrib, Finset.sum_const, ← Finset.card_filter]
    simp [uB, Finset.card_univ, Fintype.card_fin]
  have hsumB_le : ∑ c : Fin k, maxcut_complete_graph_optimal_strong_cls τ c ≤ k * q + uB := by
    calc ∑ c : Fin k, maxcut_complete_graph_optimal_strong_cls τ c
        ≤ ∑ c : Fin k, (q + (if maxcut_complete_graph_optimal_strong_cls τ c = q + 1 then 1 else 0)) :=
          Finset.sum_le_sum (fun c _ => hB_bound c)
      _ = k * q + uB := hBsum_aux
  have hu_le : uA ≤ uB := by
    have h1 : n ≤ k * q + uB := hsumB ▸ hsumB_le
    have h2 : k * q + uA = n := by rw [← hsumA_eq]; exact hsumA
    omega
  have hsub : (Finset.univ.filter fun c : Fin k => maxcut_complete_graph_optimal_strong_cls τ c = q + 1)
      ⊆ (Finset.univ.filter fun c : Fin k => maxcut_complete_graph_optimal_strong_cls σ c = q + 1) := by
    intro c hc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hc ⊢
    exact hAB c hc
  have huB_le : uB ≤ uA := by
    have := Finset.card_le_card hsub
    simpa [uA, uB] using this
  have hueq : uA = uB := le_antisymm hu_le huB_le
  have hset_eq : (Finset.univ.filter fun c : Fin k => maxcut_complete_graph_optimal_strong_cls σ c = q + 1)
      = (Finset.univ.filter fun c : Fin k => maxcut_complete_graph_optimal_strong_cls τ c = q + 1) := by
    have h := Finset.eq_of_subset_of_card_le hsub (by simpa [uA, uB] using hu_le)
    exact h.symm
  have hBsum_eq : ∑ c : Fin k, maxcut_complete_graph_optimal_strong_cls τ c
      = ∑ c : Fin k, (q + (if maxcut_complete_graph_optimal_strong_cls τ c = q + 1 then 1 else 0)) := by
    rw [hBsum_aux, ← hueq, ← hsumA_eq]
    exact hsumB.trans hsumA.symm
  have hB_ge : ∀ c : Fin k, q ≤ maxcut_complete_graph_optimal_strong_cls τ c := by
    intro c
    have hpt := (Finset.sum_eq_sum_iff_of_le (fun i _ => hB_bound i)).mp hBsum_eq c (Finset.mem_univ c)
    split_ifs at hpt with hh <;> omega
  obtain ⟨v, hvS⟩ := hSne
  have h1 := hstep1 v hvS
  have hBv := hB_ge (τ v)
  have hAv := hA_le (σ v)
  have hB_eq_q : maxcut_complete_graph_optimal_strong_cls τ (τ v) = q := by omega
  have hA_eq_q1 : maxcut_complete_graph_optimal_strong_cls σ (σ v) = q + 1 := by omega
  have hmem : σ v ∈ (Finset.univ.filter fun c : Fin k =>
      maxcut_complete_graph_optimal_strong_cls σ c = q + 1) := by
    simp [hA_eq_q1]
  rw [hset_eq] at hmem
  have hB_sv : maxcut_complete_graph_optimal_strong_cls τ (σ v) = q + 1 := by simpa using hmem
  have hEzero := hEq_of_B (σ v) hB_sv
  have hEpos : 0 < maxcut_complete_graph_optimal_strong_clsS σ S (σ v) := by
    apply Finset.card_pos.mpr
    exact ⟨v, by simp [hvS]⟩
  omega
