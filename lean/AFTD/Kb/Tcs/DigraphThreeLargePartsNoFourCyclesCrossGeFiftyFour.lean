import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphDirectedCycleOn
import AFTD.Kb.Tcs.DigraphPackingFreeCutPeelingBound
import AFTD.Kb.Tcs.DigraphSevenOutRobustTwoCycleFreeCutGeTwenty
import AFTD.Kb.Tcs.DigraphThreeLargePartsNoFourCyclesCrossGeFortyFive

/-!
# digraph_three_large_parts_no_four_cycles_cross_ge_fifty_four

Topic: graphs   Node: 80733bfd1e9a

Provenance: helper lemma. Partition cut reduction for OP-110; experiments 12598 and 12606 check the degree and cycle-allocation arithmetic.

If a finite digraph of minimum outdegree seven has no four disjoint directed cycles and its vertices are partitioned into three parts each of size at least seven, then at least 54 arcs cross between parts, assuming the displayed one-, robust two- and three-cycle criteria.
-/

set_option maxHeartbeats 3000000
set_option maxRecDepth 4096
private lemma in833_cut_sum_of_two
    (α : Type) [Fintype α] [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj]
    (col : α → Fin 3)
    (hsize : ∀ i, 7 ≤ (Finset.univ.filter fun v => col v = i).card)
    (hdeg : ∀ v, 7 ≤ (Finset.univ.filter fun w => D.Adj v w).card)
    (hone : ∀ T : Finset α, T.Nonempty →
      (∀ v ∈ T, 1 ≤ (T.filter fun w => D.Adj v w).card) →
      ∃ C : Finset α, C ⊆ T ∧ digraph_directed_cycle_on D C)
    (htwo : ∀ T : Finset α, T.Nonempty →
      (∀ v ∈ T, 2 ≤ (T.filter fun w => D.Adj v w).card) →
      (T.filter fun v => (T.filter fun w => D.Adj v w).card < 3).card ≤ 2 →
      ∃ c : Fin 2 → Finset α, (∀ i, c i ⊆ T ∧ digraph_directed_cycle_on D (c i)) ∧
        Pairwise (fun i j => Disjoint (c i) (c j)))
    (hthree : ∀ T : Finset α, T.Nonempty →
      (∀ v ∈ T, 5 ≤ (T.filter fun w => D.Adj v w).card) →
      ∃ c : Fin 3 → Finset α, (∀ i, c i ⊆ T ∧ digraph_directed_cycle_on D (c i)) ∧
        Pairwise (fun i j => Disjoint (c i) (c j)))
    (hno : ¬ ∃ c : Fin 4 → Finset α,
      (∀ i, digraph_directed_cycle_on D (c i)) ∧
        Pairwise (fun i j => Disjoint (c i) (c j)))
    (i j k : Fin 3) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (h2 : digraph_three_large_parts_no_four_cycles_cross_ge_forty_five_has_pack2 D (Finset.univ.filter fun v => col v = i)) :
    54 ≤ ∑ v ∈ (Finset.univ.filter fun v => col v = i), ((Finset.univ.filter fun v => col v = i)ᶜ.filter fun w => D.Adj v w).card +
         ∑ v ∈ (Finset.univ.filter fun v => col v = j), ((Finset.univ.filter fun v => col v = j)ᶜ.filter fun w => D.Adj v w).card +
         ∑ v ∈ (Finset.univ.filter fun v => col v = k), ((Finset.univ.filter fun v => col v = k)ᶜ.filter fun w => D.Adj v w).card := by
  let B (m : Fin 3) := Finset.univ.filter fun v => col v = m
  let cut (m : Fin 3) := ∑ v ∈ B m, ((B m)ᶜ.filter fun w => D.Adj v w).card
  change 54 ≤ cut i + cut j + cut k
  have hcut1 : ∀ m : Fin 3, ¬ digraph_three_large_parts_no_four_cycles_cross_ge_forty_five_has_pack1 D (B m) → 28 ≤ cut m := by
    intro m hm1
    have hcriterion : ∀ T : Finset α, T.Nonempty →
        (∀ v ∈ T, 1 ≤ (T.filter fun w => D.Adj v w).card) →
        ∃ c : Fin 1 → Finset α, (∀ i, c i ⊆ T ∧ digraph_directed_cycle_on D (c i)) ∧
          Pairwise (fun i j => Disjoint (c i) (c j)) := by
      intro T hT hd
      obtain ⟨C, hC1, hC2⟩ := hone T hT hd
      refine ⟨fun _ => C, fun _ => ⟨hC1, hC2⟩, ?_⟩
      intro a b hab; fin_cases a; fin_cases b; contradiction
    have hno_q : ¬ ∃ c : Fin 1 → Finset α, (∀ i, c i ⊆ B m ∧ digraph_directed_cycle_on D (c i)) ∧
          Pairwise (fun i j => Disjoint (c i) (c j)) := by
      intro ⟨c, hc, _⟩; exact hm1 ⟨c 0, (hc 0).1, (hc 0).2⟩
    have hBm : 7 - 1 + 1 ≤ (B m).card := by dsimp [B]; have := hsize m; omega
    have hbound := digraph_packing_free_cut_peeling_bound α D 7 1 1 (by omega) (B m) hBm
      (fun v _ => hdeg v) hcriterion hno_q
    have hcalc : (7 - 1 + 1) * (7 - 1 + 2) / 2 = 28 := by rfl
    rwa [hcalc] at hbound
  have hcut2 : ∀ m : Fin 3, ¬ digraph_three_large_parts_no_four_cycles_cross_ge_forty_five_has_pack2 D (B m) → 20 ≤ cut m := by
    intro m hm2
    exact digraph_seven_out_robust_two_cycle_free_cut_ge_twenty α D (B m) (hsize m) (fun v _ => hdeg v) htwo hm2
  have hcut3 : ∀ m : Fin 3, ¬ digraph_three_large_parts_no_four_cycles_cross_ge_forty_five_has_pack3 D (B m) → 6 ≤ cut m := by
    intro m hm3
    have hBm : 7 - 5 + 1 ≤ (B m).card := by dsimp [B]; have := hsize m; omega
    have hbound := digraph_packing_free_cut_peeling_bound α D 7 5 3 (by omega) (B m) hBm
      (fun v _ => hdeg v) hthree (by exact hm3)
    have hcalc : (7 - 5 + 1) * (7 - 5 + 2) / 2 = 6 := by rfl
    rwa [hcalc] at hbound
  by_cases h3 : digraph_three_large_parts_no_four_cycles_cross_ge_forty_five_has_pack3 D (B i)
  · have hj1 : ¬ digraph_three_large_parts_no_four_cycles_cross_ge_forty_five_has_pack1 D (B j) :=
      fun hj => digraph_three_large_parts_no_four_cycles_cross_ge_forty_five_no_three_one D col hno hij h3 hj
    have hk1 : ¬ digraph_three_large_parts_no_four_cycles_cross_ge_forty_five_has_pack1 D (B k) :=
      fun hk => digraph_three_large_parts_no_four_cycles_cross_ge_forty_five_no_three_one D col hno hik h3 hk
    have bnd_j := hcut1 j hj1
    have bnd_k := hcut1 k hk1
    omega
  · have bnd_i := hcut3 i h3
    have hj2 : ¬ digraph_three_large_parts_no_four_cycles_cross_ge_forty_five_has_pack2 D (B j) :=
      fun hj => digraph_three_large_parts_no_four_cycles_cross_ge_forty_five_no_two_two D col hno hij h2 hj
    have hk2 : ¬ digraph_three_large_parts_no_four_cycles_cross_ge_forty_five_has_pack2 D (B k) :=
      fun hk => digraph_three_large_parts_no_four_cycles_cross_ge_forty_five_no_two_two D col hno hik h2 hk
    have bnd_j2 := hcut2 j hj2
    have bnd_k2 := hcut2 k hk2
    by_cases hj1 : digraph_three_large_parts_no_four_cycles_cross_ge_forty_five_has_pack1 D (B j)
    · have hk1 : ¬ digraph_three_large_parts_no_four_cycles_cross_ge_forty_five_has_pack1 D (B k) :=
        fun hk => digraph_three_large_parts_no_four_cycles_cross_ge_forty_five_no_two_one_one D col hno hij hik hjk h2 hj1 hk
      have bnd_k1 := hcut1 k hk1
      omega
    · have bnd_j1 := hcut1 j hj1
      omega

theorem digraph_three_large_parts_no_four_cycles_cross_ge_fifty_four
    (α : Type) [Fintype α] [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj]
    (col : α → Fin 3)
    (hsize : ∀ i, 7 ≤ (Finset.univ.filter fun v => col v = i).card)
    (hdeg : ∀ v, 7 ≤ (Finset.univ.filter fun w => D.Adj v w).card)
    (hone : ∀ T : Finset α, T.Nonempty →
      (∀ v ∈ T, 1 ≤ (T.filter fun w => D.Adj v w).card) →
      ∃ C : Finset α, C ⊆ T ∧ digraph_directed_cycle_on D C)
    (htwo : ∀ T : Finset α, T.Nonempty →
      (∀ v ∈ T, 2 ≤ (T.filter fun w => D.Adj v w).card) →
      (T.filter fun v => (T.filter fun w => D.Adj v w).card < 3).card ≤ 2 →
      ∃ c : Fin 2 → Finset α, (∀ i, c i ⊆ T ∧ digraph_directed_cycle_on D (c i)) ∧
        Pairwise (fun i j => Disjoint (c i) (c j)))
    (hthree : ∀ T : Finset α, T.Nonempty →
      (∀ v ∈ T, 5 ≤ (T.filter fun w => D.Adj v w).card) →
      ∃ c : Fin 3 → Finset α, (∀ i, c i ⊆ T ∧ digraph_directed_cycle_on D (c i)) ∧
        Pairwise (fun i j => Disjoint (c i) (c j)))
    (hno : ¬ ∃ c : Fin 4 → Finset α,
      (∀ i, digraph_directed_cycle_on D (c i)) ∧
        Pairwise (fun i j => Disjoint (c i) (c j))) :
    54 ≤ ∑ v : α, (Finset.univ.filter fun w => col w ≠ col v ∧ D.Adj v w).card := by
  have hcross : ∑ v : α, (Finset.univ.filter fun w => col w ≠ col v ∧ D.Adj v w).card =
      ∑ i : Fin 3, ∑ v ∈ (Finset.univ.filter fun v => col v = i),
        ((Finset.univ.filter fun v => col v = i)ᶜ.filter fun w => D.Adj v w).card := by
    rw [← Finset.sum_fiberwise Finset.univ col]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    congr 1
    ext w
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_compl]
    constructor
    · rintro ⟨hne, hadj⟩
      refine ⟨?_, hadj⟩
      intro hw
      exact hne (hw.trans hv.symm)
    · rintro ⟨hw, hadj⟩
      refine ⟨?_, hadj⟩
      intro heq
      apply hw
      exact heq.trans hv
  rw [hcross, Fin.sum_univ_three]
  let cut (m : Fin 3) := ∑ v ∈ (Finset.univ.filter fun v => col v = m),
    ((Finset.univ.filter fun v => col v = m)ᶜ.filter fun w => D.Adj v w).card
  change 54 ≤ cut 0 + cut 1 + cut 2
  by_cases h : ∃ i : Fin 3, digraph_three_large_parts_no_four_cycles_cross_ge_forty_five_has_pack2 D (Finset.univ.filter fun v => col v = i)
  · obtain ⟨i, hi⟩ := h
    fin_cases i
    · have h0 := in833_cut_sum_of_two α D col hsize hdeg hone htwo hthree hno 0 1 2
        (by decide) (by decide) (by decide) hi
      dsimp [cut]
      exact h0
    · have h1 := in833_cut_sum_of_two α D col hsize hdeg hone htwo hthree hno 1 0 2
        (by decide) (by decide) (by decide) hi
      dsimp [cut] at *
      omega
    · have h2 := in833_cut_sum_of_two α D col hsize hdeg hone htwo hthree hno 2 0 1
        (by decide) (by decide) (by decide) hi
      dsimp [cut] at *
      omega
  · have hnot : ∀ m : Fin 3, ¬ digraph_three_large_parts_no_four_cycles_cross_ge_forty_five_has_pack2 D (Finset.univ.filter fun v => col v = m) := by
      intro m hm; exact h ⟨m, hm⟩
    have hcut2 : ∀ m : Fin 3, 20 ≤ cut m := by
      intro m
      exact digraph_seven_out_robust_two_cycle_free_cut_ge_twenty α D (Finset.univ.filter fun v => col v = m)
        (hsize m) (fun v _ => hdeg v) htwo (hnot m)
    have c0 := hcut2 0
    have c1 := hcut2 1
    have c2 := hcut2 2
    omega
