import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphDirectedCycleOn
import AFTD.Kb.Tcs.DigraphSevenOutRobustCutThresholds
import AFTD.Kb.Tcs.DigraphCutTwentySuperlevelEqualityPatterns

/-!
# digraph_twenty_cut_degree_profile_under_two_cycle_sequences

Topic: graphs   Node: 3336679ce123

Provenance: helper lemma. Degree-sequence criterion in https://arxiv.org/abs/2205.10826, Definition 1.3 and Theorem 1.4; experiments 26240, 26253 and 26254.

For a seven-outregular two-cycle-free part with a twenty-arc outgoing cut, the displayed robust and two-cycle degree-sequence criteria force outside-degree multiset 6,5,4,3,2 and zeros.
-/

theorem digraph_twenty_cut_degree_profile_under_two_cycle_sequences
    (α : Type) [Fintype α] [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj]
    (B : Finset α) (hB : 7 ≤ B.card)
    (hdeg : ∀ v ∈ B, (Finset.univ.filter fun w => D.Adj v w).card = 7)
    (hrobust : ∀ T : Finset α, T.Nonempty →
      (∀ v ∈ T, 2 ≤ (T.filter fun w => D.Adj v w).card) →
      (T.filter fun v => (T.filter fun w => D.Adj v w).card < 3).card ≤ 2 →
      ∃ c : Fin 2 → Finset α, (∀ i, c i ⊆ T ∧ digraph_directed_cycle_on D (c i)) ∧
        Pairwise (fun i j => Disjoint (c i) (c j)))
    (hseq1 : (∀ v ∈ B, 2 ≤ (B.filter fun w => D.Adj v w).card) →
      (B.filter fun v => (B.filter fun w => D.Adj v w).card < 4).card ≤ 3 →
      ∃ c : Fin 2 → Finset α, (∀ i, c i ⊆ B ∧ digraph_directed_cycle_on D (c i)) ∧
        Pairwise (fun i j => Disjoint (c i) (c j)))
    (hseq2 : (∀ v ∈ B, 1 ≤ (B.filter fun w => D.Adj v w).card) →
      (B.filter fun v => (B.filter fun w => D.Adj v w).card < 3).card ≤ 1 →
      (B.filter fun v => (B.filter fun w => D.Adj v w).card < 4).card ≤ 4 →
      ∃ c : Fin 2 → Finset α, (∀ i, c i ⊆ B ∧ digraph_directed_cycle_on D (c i)) ∧
        Pairwise (fun i j => Disjoint (c i) (c j)))
    (hseq3 : (∀ v ∈ B, 1 ≤ (B.filter fun w => D.Adj v w).card) →
      (B.filter fun v => (B.filter fun w => D.Adj v w).card < 4).card ≤ 2 →
      (B.filter fun v => (B.filter fun w => D.Adj v w).card < 5).card ≤ 6 →
      ∃ c : Fin 2 → Finset α, (∀ i, c i ⊆ B ∧ digraph_directed_cycle_on D (c i)) ∧
        Pairwise (fun i j => Disjoint (c i) (c j)))
    (hno : ¬ ∃ c : Fin 2 → Finset α,
      (∀ i, c i ⊆ B ∧ digraph_directed_cycle_on D (c i)) ∧
        Pairwise (fun i j => Disjoint (c i) (c j)))
    (hcut : (∑ v ∈ B, (Bᶜ.filter fun w => D.Adj v w).card) = 20) :
    let N := fun k : ℕ => (B.filter fun v => k ≤ (Bᶜ.filter fun w => D.Adj v w).card).card
    N 1 = 5 ∧ N 2 = 5 ∧ N 3 = 4 ∧ N 4 = 3 ∧ N 5 = 2 ∧ N 6 = 1 := by
  classical
  set d : α → ℕ := fun v => (Bᶜ.filter fun w => D.Adj v w).card with hd
  set n : ℕ → ℕ := fun k => (B.filter fun v => k ≤ d v).card with hn
  change n 1 = 5 ∧ n 2 = 5 ∧ n 3 = 4 ∧ n 4 = 3 ∧ n 5 = 2 ∧ n 6 = 1
  have hdeg7 : ∀ v ∈ B, 7 ≤ (Finset.univ.filter fun w => D.Adj v w).card :=
    fun v hv => le_of_eq (hdeg v hv).symm
  have hth := digraph_seven_out_robust_cut_thresholds α D B hB hdeg7 hrobust hno
  have hth' : (1 ≤ n 6 ∨ 3 ≤ n 5) ∧ (2 ≤ n 5 ∨ 4 ≤ n 4) ∧
      (3 ≤ n 4 ∨ 5 ≤ n 3) ∧ (4 ≤ n 3 ∨ 6 ≤ n 2) ∧ (5 ≤ n 2 ∨ 7 ≤ n 1) := hth
  have hab : ∀ v ∈ B, (B.filter fun w => D.Adj v w).card + d v = 7 := by
    intro v hv
    show (B.filter fun w => D.Adj v w).card + (Bᶜ.filter fun w => D.Adj v w).card = 7
    have hunion : (B.filter fun w => D.Adj v w).card + (Bᶜ.filter fun w => D.Adj v w).card
        = (Finset.univ.filter fun w => D.Adj v w).card := by
      rw [← Finset.card_union_of_disjoint]
      · congr 1
        rw [← Finset.filter_union, Finset.union_compl]
      · rw [Finset.disjoint_left]
        intro a ha ha'
        simp only [Finset.mem_filter] at ha ha'
        exact (Finset.mem_compl.mp ha'.1) ha.1
    have h7 := hdeg v hv
    omega
  have hAlt : ∀ (k : ℕ), 1 ≤ k → k ≤ 7 →
      (B.filter fun v => (B.filter fun w => D.Adj v w).card < k).card = n (8 - k) := by
    intro k hk1 hk7
    have hfe : (B.filter fun v => (B.filter fun w => D.Adj v w).card < k)
        = (B.filter fun v => 8 - k ≤ d v) := by
      apply Finset.filter_congr
      intro v hv
      have h := hab v hv
      constructor <;> intro hh <;> omega
    rw [hfe]
  have hmono : n 6 ≤ n 5 ∧ n 5 ≤ n 4 ∧ n 4 ≤ n 3 ∧ n 3 ≤ n 2 ∧ n 2 ≤ n 1 := by
    have key : ∀ a b : ℕ, a ≤ b → n b ≤ n a := by
      intro a b hab'
      show (B.filter fun v => b ≤ d v).card ≤ (B.filter fun v => a ≤ d v).card
      apply Finset.card_le_card
      intro v hv
      simp only [Finset.mem_filter] at hv ⊢
      exact ⟨hv.1, le_trans hab' hv.2⟩
    exact ⟨key 5 6 (by norm_num), key 4 5 (by norm_num), key 3 4 (by norm_num),
      key 2 3 (by norm_num), key 1 2 (by norm_num)⟩
  have hkey : ∀ m : ℕ, m ≤ 7 → (∑ k ∈ Finset.range 7, (if k + 1 ≤ m then (1:ℕ) else 0)) = m := by
    intro m hm
    rw [← Finset.sum_filter]
    have hf : (Finset.range 7).filter (fun k => k + 1 ≤ m) = Finset.range m := by
      ext k
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    rw [hf, ← Finset.card_eq_sum_ones, Finset.card_range]
  have hIcc : ∑ k ∈ Finset.range 7, n (k + 1) = 20 := by
    calc ∑ k ∈ Finset.range 7, n (k + 1)
        = ∑ k ∈ Finset.range 7, ∑ v ∈ B, (if k + 1 ≤ d v then (1:ℕ) else 0) := by
          apply Finset.sum_congr rfl
          intro k hk
          show n (k+1) = ∑ v ∈ B, (if k + 1 ≤ d v then (1:ℕ) else 0)
          rw [show n (k+1) = (B.filter fun v => k + 1 ≤ d v).card from by simp only [hn]]
          exact Finset.card_filter (fun v => k + 1 ≤ d v) B
      _ = ∑ v ∈ B, ∑ k ∈ Finset.range 7, (if k + 1 ≤ d v then (1:ℕ) else 0) := Finset.sum_comm
      _ = ∑ v ∈ B, d v := by
          apply Finset.sum_congr rfl
          intro v hv
          exact hkey (d v) (by have h := hab v hv; omega)
      _ = 20 := by simpa only [hd] using hcut
  have hsum7 : n 1 + n 2 + n 3 + n 4 + n 5 + n 6 + n 7 = 20 := by
    have h := hIcc
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.reduceAdd] at h
    omega
  have harith : 20 ≤ n 1 + n 2 + n 3 + n 4 + n 5 + n 6 := by
    obtain ⟨m65, m54, m43, m32, m21⟩ := hmono
    obtain ⟨a1, a2, a3, a4, a5⟩ := hth'
    rcases a1 with h | h <;> rcases a2 with h' | h' <;> rcases a3 with h'' | h'' <;>
      rcases a4 with h''' | h''' <;> rcases a5 with h'''' | h'''' <;> omega
  have hn7 : n 7 = 0 := by omega
  have hnsum : n 1 + n 2 + n 3 + n 4 + n 5 + n 6 = 20 := by omega
  have hpat := digraph_cut_twenty_superlevel_equality_patterns (n 1) (n 2) (n 3) (n 4) (n 5) (n 6)
    hmono hnsum hth'.1 hth'.2.1 hth'.2.2.1 hth'.2.2.2.1 hth'.2.2.2.2
  have hge : ∀ (k c : ℕ), 1 ≤ k → k ≤ 7 → 8 - k = c → n c = 0 →
      ∀ v ∈ B, k ≤ (B.filter fun w => D.Adj v w).card := by
    intro k c hk1 hk7 hkc hnc v hv
    by_contra h
    rw [Nat.not_le] at h
    have hmem : v ∈ B.filter (fun v => (B.filter fun w => D.Adj v w).card < k) :=
      Finset.mem_filter.2 ⟨hv, h⟩
    have hcard : 0 < (B.filter (fun v => (B.filter fun w => D.Adj v w).card < k)).card :=
      Finset.card_pos.2 ⟨v, hmem⟩
    rw [hAlt k hk1 hk7, hkc] at hcard
    omega
  rcases hpat with hp | hp | hp | hp
  · obtain ⟨e1, e2, e3, e4, e5, e6⟩ := hp
    exfalso
    apply hno
    apply hseq1
    · exact hge 2 6 (by norm_num) (by norm_num) (by norm_num) e6
    · have eq4 : n (8 - 4) = n 4 := by norm_num
      have k4 := hAlt 4 (by norm_num) (by norm_num)
      omega
  · obtain ⟨e1, e2, e3, e4, e5, e6⟩ := hp
    exfalso
    apply hno
    apply hseq2
    · exact hge 1 7 (by norm_num) (by norm_num) (by norm_num) hn7
    · have eq3 : n (8 - 3) = n 5 := by norm_num
      have k3 := hAlt 3 (by norm_num) (by norm_num)
      omega
    · have eq4 : n (8 - 4) = n 4 := by norm_num
      have k4 := hAlt 4 (by norm_num) (by norm_num)
      omega
  · obtain ⟨e1, e2, e3, e4, e5, e6⟩ := hp
    exfalso
    apply hno
    apply hseq3
    · exact hge 1 7 (by norm_num) (by norm_num) (by norm_num) hn7
    · have eq4 : n (8 - 4) = n 4 := by norm_num
      have k4 := hAlt 4 (by norm_num) (by norm_num)
      omega
    · have eq5 : n (8 - 5) = n 3 := by norm_num
      have k5 := hAlt 5 (by norm_num) (by norm_num)
      omega
  · obtain ⟨e1, e2, e3, e4, e5, e6⟩ := hp
    exact ⟨e1, e2, e3, e4, e5, e6⟩
