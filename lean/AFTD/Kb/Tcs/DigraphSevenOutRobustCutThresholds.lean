import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphDirectedCycleOn

/-!
# digraph_seven_out_robust_cut_thresholds

Topic: graphs   Node: 4b357912eed8

Provenance: helper lemma. Superlevel-count reduction for the robust cut lemma in OP-110; experiment 26115 checks the resulting arithmetic.

Under the displayed robust two-cycle criterion, if a set of at least seven vertices in a digraph of minimum outdegree seven contains no two disjoint directed cycles, then its numbers of vertices with at least each specified outside outdegree satisfy the five displayed alternatives.
-/

set_option maxHeartbeats 3000000
set_option maxRecDepth 4096
private lemma in833_select_thresholds {α : Type} [DecidableEq α] (A B : Finset α) (t : ℕ)
    (hAB : A ⊆ B) (hA : A.card ≤ t) (hB : B.card ≤ t + 2) :
    ∃ S : Finset α, S ⊆ B ∧ A ⊆ S ∧ S.card ≤ t ∧ (B \ S).card ≤ 2 := by
  by_cases hsmall : B.card ≤ t
  · exact ⟨B, Finset.Subset.rfl, hAB, hsmall, by simp⟩
  · have hd : t - A.card ≤ (B \ A).card := by
      rw [Finset.card_sdiff_of_subset hAB]
      omega
    obtain ⟨R, hRB, hRcard⟩ := Finset.exists_subset_card_eq hd
    refine ⟨A ∪ R, ?_, ?_, ?_, ?_⟩
    · exact Finset.union_subset hAB (hRB.trans (Finset.sdiff_subset))
    · exact Finset.subset_union_left
    · have hdis : Disjoint A R := by
        apply Finset.disjoint_left.mpr
        intro v hvA hvR
        exact (Finset.mem_sdiff.mp (hRB hvR)).2 hvA
      rw [Finset.card_union_of_disjoint hdis, hRcard]
      omega
    · have hsub : A ∪ R ⊆ B := Finset.union_subset hAB (hRB.trans Finset.sdiff_subset)
      have hdis : Disjoint A R := by
        apply Finset.disjoint_left.mpr
        intro v hvA hvR
        exact (Finset.mem_sdiff.mp (hRB hvR)).2 hvA
      rw [Finset.card_sdiff_of_subset hsub, Finset.card_union_of_disjoint hdis, hRcard]
      omega

private theorem in833_threshold_general
    (α : Type) [Fintype α] [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj]
    (B : Finset α) (hB : 7 ≤ B.card)
    (hdeg : ∀ v ∈ B, 7 ≤ (Finset.univ.filter fun w => D.Adj v w).card)
    (hrobust : ∀ T : Finset α, T.Nonempty →
      (∀ v ∈ T, 2 ≤ (T.filter fun w => D.Adj v w).card) →
      (T.filter fun v => (T.filter fun w => D.Adj v w).card < 3).card ≤ 2 →
      ∃ c : Fin 2 → Finset α, (∀ i, c i ⊆ T ∧ digraph_directed_cycle_on D (c i)) ∧
        Pairwise (fun i j => Disjoint (c i) (c j)))
    (hno : ¬ ∃ c : Fin 2 → Finset α,
      (∀ i, c i ⊆ B ∧ digraph_directed_cycle_on D (c i)) ∧
        Pairwise (fun i j => Disjoint (c i) (c j)))
    (t : ℕ) (ht : t ≤ 4) :
    let n : ℕ → ℕ := fun k => (B.filter fun v => k ≤ (Bᶜ.filter fun w => D.Adj v w).card).card
    t+1 ≤ n (6-t) ∨ t+3 ≤ n (5-t) := by
  classical
  let d : α → ℕ := fun v => (Bᶜ.filter fun w => D.Adj v w).card
  let A := B.filter fun v => 6-t ≤ d v
  let P := B.filter fun v => 5-t ≤ d v
  change t+1 ≤ A.card ∨ t+3 ≤ P.card
  by_contra hh
  have hA : A.card ≤ t := by omega
  have hP : P.card ≤ t+2 := by omega
  have hAP : A ⊆ P := by
    intro v hv
    have h := Finset.mem_filter.mp hv
    exact Finset.mem_filter.mpr ⟨h.1, by omega⟩
  obtain ⟨S,hSP,hAS,hScard,hPS⟩ := in833_select_thresholds A P t hAP hA hP
  have hPB : P ⊆ B := Finset.filter_subset _ _
  have hSB : S ⊆ B := hSP.trans hPB
  let T := B \ S
  have hT : T.Nonempty := by
    apply Finset.card_pos.mp
    change 0 < (B \ S).card
    have h := Finset.card_sdiff_add_card_eq_card hSB
    omega
  have hsum (v : α) (hv : v ∈ B) :
      7 ≤ (T.filter fun w => D.Adj v w).card + S.card + d v := by
    have hsubset : (Finset.univ.filter fun w => D.Adj v w) ⊆
        (T.filter fun w => D.Adj v w) ∪ S ∪ (Bᶜ.filter fun w => D.Adj v w) := by
      intro w hw
      have hadj := (Finset.mem_filter.mp hw).2
      by_cases hwB : w ∈ B
      · by_cases hwS : w ∈ S
        · exact Finset.mem_union_left _ (Finset.mem_union_right _ hwS)
        · apply Finset.mem_union_left
          apply Finset.mem_union_left
          exact Finset.mem_filter.mpr ⟨Finset.mem_sdiff.mpr ⟨hwB,hwS⟩,hadj⟩
      · apply Finset.mem_union_right
        exact Finset.mem_filter.mpr ⟨Finset.mem_compl.mpr hwB,hadj⟩
    have hc := Finset.card_le_card hsubset
    have hu1 := Finset.card_union_le ((T.filter fun w => D.Adj v w) ∪ S) (Bᶜ.filter fun w => D.Adj v w)
    have hu2 := Finset.card_union_le (T.filter fun w => D.Adj v w) S
    have hvdeg := hdeg v hv
    dsimp [d]
    omega
  have hTdeg : ∀ v ∈ T, 2 ≤ (T.filter fun w => D.Adj v w).card := by
    intro v hv
    have hvB := (Finset.mem_sdiff.mp hv).1
    have hvS := (Finset.mem_sdiff.mp hv).2
    have hvA : v ∉ A := fun ha => hvS (hAS ha)
    have hd : d v < 6-t := by
      by_contra h
      exact hvA (Finset.mem_filter.mpr ⟨hvB, by omega⟩)
    have hn := hsum v hvB
    omega
  have hbadsub : (T.filter fun v => (T.filter fun w => D.Adj v w).card < 3) ⊆ P \ S := by
    intro v hv
    obtain ⟨hvT,hvlow⟩ := Finset.mem_filter.mp hv
    have hvB := (Finset.mem_sdiff.mp hvT).1
    have hvS := (Finset.mem_sdiff.mp hvT).2
    have hn := hsum v hvB
    have hvP : v ∈ P := Finset.mem_filter.mpr ⟨hvB, by omega⟩
    exact Finset.mem_sdiff.mpr ⟨hvP,hvS⟩
  have hbad : (T.filter fun v => (T.filter fun w => D.Adj v w).card < 3).card ≤ 2 :=
    (Finset.card_le_card hbadsub).trans hPS
  obtain ⟨c,hc,hpair⟩ := hrobust T hT hTdeg hbad
  apply hno
  refine ⟨c, ?_, hpair⟩
  intro i
  exact ⟨(hc i).1.trans (Finset.sdiff_subset), (hc i).2⟩

theorem digraph_seven_out_robust_cut_thresholds
    (α : Type) [Fintype α] [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj]
    (B : Finset α) (hB : 7 ≤ B.card)
    (hdeg : ∀ v ∈ B, 7 ≤ (Finset.univ.filter fun w => D.Adj v w).card)
    (hrobust : ∀ T : Finset α, T.Nonempty →
      (∀ v ∈ T, 2 ≤ (T.filter fun w => D.Adj v w).card) →
      (T.filter fun v => (T.filter fun w => D.Adj v w).card < 3).card ≤ 2 →
      ∃ c : Fin 2 → Finset α, (∀ i, c i ⊆ T ∧ digraph_directed_cycle_on D (c i)) ∧
        Pairwise (fun i j => Disjoint (c i) (c j)))
    (hno : ¬ ∃ c : Fin 2 → Finset α,
      (∀ i, c i ⊆ B ∧ digraph_directed_cycle_on D (c i)) ∧
        Pairwise (fun i j => Disjoint (c i) (c j))) :
    let n : ℕ → ℕ := fun k => (B.filter fun v => k ≤ (Bᶜ.filter fun w => D.Adj v w).card).card
    (1 ≤ n 6 ∨ 3 ≤ n 5) ∧ (2 ≤ n 5 ∨ 4 ≤ n 4) ∧
    (3 ≤ n 4 ∨ 5 ≤ n 3) ∧ (4 ≤ n 3 ∨ 6 ≤ n 2) ∧ (5 ≤ n 2 ∨ 7 ≤ n 1) := by
  classical
  let d : α → ℕ := fun v => (Bᶜ.filter fun w => D.Adj v w).card
  let n : ℕ → ℕ := fun k => (B.filter fun v => k ≤ d v).card
  change (1 ≤ n 6 ∨ 3 ≤ n 5) ∧ (2 ≤ n 5 ∨ 4 ≤ n 4) ∧
    (3 ≤ n 4 ∨ 5 ≤ n 3) ∧ (4 ≤ n 3 ∨ 6 ≤ n 2) ∧ (5 ≤ n 2 ∨ 7 ≤ n 1)
  have h0 := in833_threshold_general α D B hB hdeg hrobust hno 0 (by omega)
  have h1 := in833_threshold_general α D B hB hdeg hrobust hno 1 (by omega)
  have h2 := in833_threshold_general α D B hB hdeg hrobust hno 2 (by omega)
  have h3 := in833_threshold_general α D B hB hdeg hrobust hno 3 (by omega)
  have h4 := in833_threshold_general α D B hB hdeg hrobust hno 4 (by omega)
  change 1 ≤ n 6 ∨ 3 ≤ n 5 at h0
  change 2 ≤ n 5 ∨ 4 ≤ n 4 at h1
  change 3 ≤ n 4 ∨ 5 ≤ n 3 at h2
  change 4 ≤ n 3 ∨ 6 ≤ n 2 at h3
  change 5 ≤ n 2 ∨ 7 ≤ n 1 at h4
  exact ⟨h0,h1,h2,h3,h4⟩
