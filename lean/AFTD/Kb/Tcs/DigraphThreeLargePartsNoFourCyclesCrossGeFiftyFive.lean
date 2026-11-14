import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphThreeLargePartsNoFourCyclesCrossGeFiftyFour
import AFTD.Kb.Tcs.DigraphThreeLargePartsNoFourCyclesCrossGeFortyFive
import AFTD.Kb.Tcs.DigraphPackingFreeCutPeelingBound
import AFTD.Kb.Tcs.DigraphDirectedCycleOn

/-!
# digraph_three_large_parts_no_four_cycles_cross_ge_fifty_five

Topic: graphs   Node: 5b910a876119

Provenance: helper lemma. Conditional sharpening of digraph_three_large_parts_no_four_cycles_cross_ge_fifty_four for the overlap-bounded equality route.

If a finite digraph of minimum outdegree seven has no four disjoint directed cycles, its vertices are partitioned into three parts of size at least seven, and the displayed one-, three-cycle and strengthened two-cycle-free cut criteria hold, then at least 55 arcs cross the parts.
-/

private lemma digraph_three_large_parts_no_four_cycles_cross_ge_fifty_five_cross_split
    (α : Type) [Fintype α] [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj]
    (col : α → Fin 3) :
    ∑ v : α, (Finset.univ.filter fun w => col w ≠ col v ∧ D.Adj v w).card =
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

private lemma digraph_three_large_parts_no_four_cycles_cross_ge_fifty_five_combine31
    (α : Type) [DecidableEq α] (D : Digraph α)
    (hno : ¬ ∃ c : Fin 4 → Finset α, (∀ i, digraph_directed_cycle_on D (c i)) ∧
      Pairwise (fun i j => Disjoint (c i) (c j)))
    (S T : Finset α) (hST : Disjoint S T)
    (c : Fin 3 → Finset α) (hc : ∀ m, c m ⊆ S ∧ digraph_directed_cycle_on D (c m))
    (hcd : Pairwise (fun a b => Disjoint (c a) (c b)))
    (C : Finset α) (hC : C ⊆ T) (hCcyc : digraph_directed_cycle_on D C) : False := by
  have h01 : Disjoint (c 0) (c 1) := hcd (by decide)
  have h02 : Disjoint (c 0) (c 2) := hcd (by decide)
  have h12 : Disjoint (c 1) (c 2) := hcd (by decide)
  have h03 : Disjoint (c 0) C := hST.mono (hc 0).1 hC
  have h13 : Disjoint (c 1) C := hST.mono (hc 1).1 hC
  have h23 : Disjoint (c 2) C := hST.mono (hc 2).1 hC
  apply hno
  refine ⟨![c 0, c 1, c 2, C], ?_, ?_⟩
  · intro m
    fin_cases m
    · exact (hc 0).2
    · exact (hc 1).2
    · exact (hc 2).2
    · exact hCcyc
  · intro a b hab
    fin_cases a <;> fin_cases b <;>
      first
        | exact h01 | exact h02 | exact h12 | exact h03 | exact h13 | exact h23
        | exact h01.symm | exact h02.symm | exact h12.symm
        | exact h03.symm | exact h13.symm | exact h23.symm
        | exact absurd rfl hab

private lemma digraph_three_large_parts_no_four_cycles_cross_ge_fifty_five_combine22
    (α : Type) [DecidableEq α] (D : Digraph α)
    (hno : ¬ ∃ c : Fin 4 → Finset α, (∀ i, digraph_directed_cycle_on D (c i)) ∧
      Pairwise (fun i j => Disjoint (c i) (c j)))
    (S T : Finset α) (hST : Disjoint S T)
    (c : Fin 2 → Finset α) (hc : ∀ m, c m ⊆ S ∧ digraph_directed_cycle_on D (c m))
    (hcd : Pairwise (fun a b => Disjoint (c a) (c b)))
    (d : Fin 2 → Finset α) (hd : ∀ m, d m ⊆ T ∧ digraph_directed_cycle_on D (d m))
    (hdd : Pairwise (fun a b => Disjoint (d a) (d b))) : False := by
  have hc01 : Disjoint (c 0) (c 1) := hcd (by decide)
  have hd01 : Disjoint (d 0) (d 1) := hdd (by decide)
  have hx1 : Disjoint (c 0) (d 0) := hST.mono (hc 0).1 (hd 0).1
  have hx2 : Disjoint (c 0) (d 1) := hST.mono (hc 0).1 (hd 1).1
  have hx3 : Disjoint (c 1) (d 0) := hST.mono (hc 1).1 (hd 0).1
  have hx4 : Disjoint (c 1) (d 1) := hST.mono (hc 1).1 (hd 1).1
  apply hno
  refine ⟨![c 0, c 1, d 0, d 1], ?_, ?_⟩
  · intro m
    fin_cases m
    · exact (hc 0).2
    · exact (hc 1).2
    · exact (hd 0).2
    · exact (hd 1).2
  · intro a b hab
    fin_cases a <;> fin_cases b <;>
      first
        | exact hc01 | exact hd01 | exact hx1 | exact hx2 | exact hx3 | exact hx4
        | exact hc01.symm | exact hd01.symm | exact hx1.symm | exact hx2.symm
        | exact hx3.symm | exact hx4.symm
        | exact absurd rfl hab

private lemma digraph_three_large_parts_no_four_cycles_cross_ge_fifty_five_combine211
    (α : Type) [DecidableEq α] (D : Digraph α)
    (hno : ¬ ∃ c : Fin 4 → Finset α, (∀ i, digraph_directed_cycle_on D (c i)) ∧
      Pairwise (fun i j => Disjoint (c i) (c j)))
    (S T U : Finset α) (hST : Disjoint S T) (hSU : Disjoint S U) (hTU : Disjoint T U)
    (c : Fin 2 → Finset α) (hc : ∀ m, c m ⊆ S ∧ digraph_directed_cycle_on D (c m))
    (hcd : Pairwise (fun a b => Disjoint (c a) (c b)))
    (C : Finset α) (hC : C ⊆ T) (hCcyc : digraph_directed_cycle_on D C)
    (C' : Finset α) (hC' : C' ⊆ U) (hC'cyc : digraph_directed_cycle_on D C') : False := by
  have h01 : Disjoint (c 0) (c 1) := hcd (by decide)
  have h02 : Disjoint (c 0) C := hST.mono (hc 0).1 hC
  have h03 : Disjoint (c 0) C' := hSU.mono (hc 0).1 hC'
  have h12 : Disjoint (c 1) C := hST.mono (hc 1).1 hC
  have h13 : Disjoint (c 1) C' := hSU.mono (hc 1).1 hC'
  have h23 : Disjoint C C' := hTU.mono hC hC'
  apply hno
  refine ⟨![c 0, c 1, C, C'], ?_, ?_⟩
  · intro m
    fin_cases m
    · exact (hc 0).2
    · exact (hc 1).2
    · exact hCcyc
    · exact hC'cyc
  · intro a b hab
    fin_cases a <;> fin_cases b <;>
      first
        | exact h01 | exact h02 | exact h03 | exact h12 | exact h13 | exact h23
        | exact h01.symm | exact h02.symm | exact h03.symm
        | exact h12.symm | exact h13.symm | exact h23.symm
        | exact absurd rfl hab

private lemma digraph_three_large_parts_no_four_cycles_cross_ge_fifty_five_cut_of_acyclic
    (α : Type) [Fintype α] [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj]
    (hdeg : ∀ v, 7 ≤ (Finset.univ.filter fun w => D.Adj v w).card)
    (hone : ∀ T : Finset α, T.Nonempty →
      (∀ v ∈ T, 1 ≤ (T.filter fun w => D.Adj v w).card) →
      ∃ C : Finset α, C ⊆ T ∧ digraph_directed_cycle_on D C)
    (S : Finset α) (hS : 7 ≤ S.card)
    (hnoS : ¬ ∃ C : Finset α, C ⊆ S ∧ digraph_directed_cycle_on D C) :
    28 ≤ ∑ v ∈ S, (Sᶜ.filter fun w => D.Adj v w).card := by
  have hcrit : ∀ T : Finset α, T.Nonempty →
      (∀ v ∈ T, 1 ≤ (T.filter fun w => D.Adj v w).card) →
      ∃ c : Fin 1 → Finset α, (∀ m, c m ⊆ T ∧ digraph_directed_cycle_on D (c m)) ∧
        Pairwise (fun a b => Disjoint (c a) (c b)) := by
    intro T hT hd
    obtain ⟨C, hCT, hCcyc⟩ := hone T hT hd
    exact ⟨fun _ => C, fun m => ⟨hCT, hCcyc⟩, fun a b hab => absurd (Subsingleton.elim a b) hab⟩
  have hn1 : ¬ ∃ c : Fin 1 → Finset α, (∀ m, c m ⊆ S ∧ digraph_directed_cycle_on D (c m)) ∧
      Pairwise (fun a b => Disjoint (c a) (c b)) := by
    rintro ⟨c, hc, _⟩
    exact hnoS ⟨c 0, (hc 0).1, (hc 0).2⟩
  have hB : 7 - 1 + 1 ≤ S.card := by omega
  have h := digraph_packing_free_cut_peeling_bound α D 7 1 1 (by omega) S hB
    (fun v _ => hdeg v) hcrit hn1
  have hc : (7 - 1 + 1) * (7 - 1 + 2) / 2 = 28 := by norm_num
  rwa [hc] at h

private lemma digraph_three_large_parts_no_four_cycles_cross_ge_fifty_five_cut_of_no_three
    (α : Type) [Fintype α] [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj]
    (hdeg : ∀ v, 7 ≤ (Finset.univ.filter fun w => D.Adj v w).card)
    (hthree : ∀ T : Finset α, T.Nonempty →
      (∀ v ∈ T, 5 ≤ (T.filter fun w => D.Adj v w).card) →
      ∃ c : Fin 3 → Finset α, (∀ i, c i ⊆ T ∧ digraph_directed_cycle_on D (c i)) ∧
        Pairwise (fun i j => Disjoint (c i) (c j)))
    (S : Finset α) (hS : 7 ≤ S.card)
    (hnoS : ¬ ∃ c : Fin 3 → Finset α, (∀ m, c m ⊆ S ∧ digraph_directed_cycle_on D (c m)) ∧
      Pairwise (fun a b => Disjoint (c a) (c b))) :
    6 ≤ ∑ v ∈ S, (Sᶜ.filter fun w => D.Adj v w).card := by
  have hB : 7 - 5 + 1 ≤ S.card := by omega
  have h := digraph_packing_free_cut_peeling_bound α D 7 5 3 (by omega) S hB
    (fun v _ => hdeg v) hthree hnoS
  have hc : (7 - 5 + 1) * (7 - 5 + 2) / 2 = 6 := by norm_num
  rwa [hc] at h

theorem digraph_three_large_parts_no_four_cycles_cross_ge_fifty_five
    (α : Type) [Fintype α] [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj]
    (col : α → Fin 3)
    (hsize : ∀ i, 7 ≤ (Finset.univ.filter fun v => col v = i).card)
    (hdeg : ∀ v, 7 ≤ (Finset.univ.filter fun w => D.Adj v w).card)
    (hone : ∀ T : Finset α, T.Nonempty →
      (∀ v ∈ T, 1 ≤ (T.filter fun w => D.Adj v w).card) →
      ∃ C : Finset α, C ⊆ T ∧ digraph_directed_cycle_on D C)
    (hthree : ∀ T : Finset α, T.Nonempty →
      (∀ v ∈ T, 5 ≤ (T.filter fun w => D.Adj v w).card) →
      ∃ c : Fin 3 → Finset α, (∀ i, c i ⊆ T ∧ digraph_directed_cycle_on D (c i)) ∧
        Pairwise (fun i j => Disjoint (c i) (c j)))
    (hcut21 : ∀ B : Finset α, 7 ≤ B.card →
      (¬ ∃ c : Fin 2 → Finset α, (∀ i, c i ⊆ B ∧ digraph_directed_cycle_on D (c i)) ∧
        Pairwise (fun i j => Disjoint (c i) (c j))) →
      21 ≤ ∑ v ∈ B, (Bᶜ.filter fun w => D.Adj v w).card)
    (hno : ¬ ∃ c : Fin 4 → Finset α, (∀ i, digraph_directed_cycle_on D (c i)) ∧
      Pairwise (fun i j => Disjoint (c i) (c j))) :
    55 ≤ ∑ v : α, (Finset.univ.filter fun w => col w ≠ col v ∧ D.Adj v w).card := by
  classical
  rw [digraph_three_large_parts_no_four_cycles_cross_ge_fifty_five_cross_split α D col,
    Fin.sum_univ_three]
  let B : Fin 3 → Finset α := fun i => Finset.univ.filter fun v => col v = i
  let cut : Fin 3 → ℕ := fun i => ∑ v ∈ B i, ((B i)ᶜ.filter fun w => D.Adj v w).card
  change 55 ≤ cut 0 + cut 1 + cut 2
  have hBcard : ∀ i, 7 ≤ (B i).card := fun i => hsize i
  have hBmem : ∀ (i : Fin 3) (v : α), v ∈ B i ↔ col v = i := by
    intro i v; simp [B]
  have hBdisj : ∀ i j : Fin 3, i ≠ j → Disjoint (B i) (B j) := by
    intro i j hij
    rw [Finset.disjoint_left]
    intro v hv hv'
    rw [hBmem i v] at hv
    rw [hBmem j v] at hv'
    exact hij (hv.symm.trans hv')
  have h28 : ∀ i, ¬ (∃ C : Finset α, C ⊆ B i ∧ digraph_directed_cycle_on D C) → 28 ≤ cut i :=
    fun i hi => digraph_three_large_parts_no_four_cycles_cross_ge_fifty_five_cut_of_acyclic
      α D hdeg hone (B i) (hBcard i) hi
  have h6 : ∀ i, ¬ (∃ c : Fin 3 → Finset α,
      (∀ m, c m ⊆ B i ∧ digraph_directed_cycle_on D (c m)) ∧
        Pairwise (fun a b => Disjoint (c a) (c b))) → 6 ≤ cut i :=
    fun i hi => digraph_three_large_parts_no_four_cycles_cross_ge_fifty_five_cut_of_no_three
      α D hdeg hthree (B i) (hBcard i) hi
  have h21 : ∀ i, ¬ (∃ c : Fin 2 → Finset α,
      (∀ m, c m ⊆ B i ∧ digraph_directed_cycle_on D (c m)) ∧
        Pairwise (fun a b => Disjoint (c a) (c b))) → 21 ≤ cut i :=
    fun i hi => hcut21 (B i) (hBcard i) hi
  by_cases hP3 : ∃ i : Fin 3, (∃ c : Fin 3 → Finset α,
      (∀ m, c m ⊆ B i ∧ digraph_directed_cycle_on D (c m)) ∧
        Pairwise (fun a b => Disjoint (c a) (c b)))
  · obtain ⟨i, c, hc, hcd⟩ := hP3
    fin_cases i
    · have a1 : 28 ≤ cut 1 := h28 1 (fun hp => by
        obtain ⟨C, hC, hCcyc⟩ := hp
        exact digraph_three_large_parts_no_four_cycles_cross_ge_fifty_five_combine31
          α D hno (B 0) (B 1) (hBdisj 0 1 (by decide)) c hc hcd C hC hCcyc)
      have a2 : 28 ≤ cut 2 := h28 2 (fun hp => by
        obtain ⟨C, hC, hCcyc⟩ := hp
        exact digraph_three_large_parts_no_four_cycles_cross_ge_fifty_five_combine31
          α D hno (B 0) (B 2) (hBdisj 0 2 (by decide)) c hc hcd C hC hCcyc)
      omega
    · have a1 : 28 ≤ cut 0 := h28 0 (fun hp => by
        obtain ⟨C, hC, hCcyc⟩ := hp
        exact digraph_three_large_parts_no_four_cycles_cross_ge_fifty_five_combine31
          α D hno (B 1) (B 0) (hBdisj 1 0 (by decide)) c hc hcd C hC hCcyc)
      have a2 : 28 ≤ cut 2 := h28 2 (fun hp => by
        obtain ⟨C, hC, hCcyc⟩ := hp
        exact digraph_three_large_parts_no_four_cycles_cross_ge_fifty_five_combine31
          α D hno (B 1) (B 2) (hBdisj 1 2 (by decide)) c hc hcd C hC hCcyc)
      omega
    · have a1 : 28 ≤ cut 0 := h28 0 (fun hp => by
        obtain ⟨C, hC, hCcyc⟩ := hp
        exact digraph_three_large_parts_no_four_cycles_cross_ge_fifty_five_combine31
          α D hno (B 2) (B 0) (hBdisj 2 0 (by decide)) c hc hcd C hC hCcyc)
      have a2 : 28 ≤ cut 1 := h28 1 (fun hp => by
        obtain ⟨C, hC, hCcyc⟩ := hp
        exact digraph_three_large_parts_no_four_cycles_cross_ge_fifty_five_combine31
          α D hno (B 2) (B 1) (hBdisj 2 1 (by decide)) c hc hcd C hC hCcyc)
      omega
  · by_cases hP2 : ∃ i : Fin 3, (∃ c : Fin 2 → Finset α,
        (∀ m, c m ⊆ B i ∧ digraph_directed_cycle_on D (c m)) ∧
          Pairwise (fun a b => Disjoint (c a) (c b)))
    · obtain ⟨i, c, hc, hcd⟩ := hP2
      have hno3 : ∀ m : Fin 3, ¬ (∃ c : Fin 3 → Finset α,
          (∀ a, c a ⊆ B m ∧ digraph_directed_cycle_on D (c a)) ∧
            Pairwise (fun a b => Disjoint (c a) (c b))) := fun m hm => hP3 ⟨m, hm⟩
      fin_cases i
      · have hn2 : ∀ j : Fin 3, j ≠ 0 → ¬ (∃ d : Fin 2 → Finset α,
            (∀ m, d m ⊆ B j ∧ digraph_directed_cycle_on D (d m)) ∧
              Pairwise (fun a b => Disjoint (d a) (d b))) := fun j hj hp => by
          obtain ⟨d, hd, hdd⟩ := hp
          exact digraph_three_large_parts_no_four_cycles_cross_ge_fifty_five_combine22
            α D hno (B 0) (B j) (hBdisj 0 j (Ne.symm hj)) c hc hcd d hd hdd
        have hb0 : 6 ≤ cut 0 := h6 0 (hno3 0)
        by_cases hc1 : ∃ C : Finset α, C ⊆ B 1 ∧ digraph_directed_cycle_on D C
        · obtain ⟨C1, hC1, hC1c⟩ := hc1
          have hnp1 : ¬ (∃ C : Finset α, C ⊆ B 2 ∧ digraph_directed_cycle_on D C) :=
            fun hp => by
              obtain ⟨C2, hC2, hC2c⟩ := hp
              exact digraph_three_large_parts_no_four_cycles_cross_ge_fifty_five_combine211
                α D hno (B 0) (B 1) (B 2) (hBdisj 0 1 (by decide)) (hBdisj 0 2 (by decide))
                (hBdisj 1 2 (by decide)) c hc hcd C1 hC1 hC1c C2 hC2 hC2c
          have b1 : 21 ≤ cut 1 := h21 1 (hn2 1 (by decide))
          have b2 : 28 ≤ cut 2 := h28 2 hnp1
          omega
        · have b1 : 28 ≤ cut 1 := h28 1 hc1
          have b2 : 21 ≤ cut 2 := h21 2 (hn2 2 (by decide))
          omega
      · have hn2 : ∀ j : Fin 3, j ≠ 1 → ¬ (∃ d : Fin 2 → Finset α,
            (∀ m, d m ⊆ B j ∧ digraph_directed_cycle_on D (d m)) ∧
              Pairwise (fun a b => Disjoint (d a) (d b))) := fun j hj hp => by
          obtain ⟨d, hd, hdd⟩ := hp
          exact digraph_three_large_parts_no_four_cycles_cross_ge_fifty_five_combine22
            α D hno (B 1) (B j) (hBdisj 1 j (Ne.symm hj)) c hc hcd d hd hdd
        have hb1 : 6 ≤ cut 1 := h6 1 (hno3 1)
        by_cases hc0 : ∃ C : Finset α, C ⊆ B 0 ∧ digraph_directed_cycle_on D C
        · obtain ⟨C1, hC1, hC1c⟩ := hc0
          have hnp1 : ¬ (∃ C : Finset α, C ⊆ B 2 ∧ digraph_directed_cycle_on D C) :=
            fun hp => by
              obtain ⟨C2, hC2, hC2c⟩ := hp
              exact digraph_three_large_parts_no_four_cycles_cross_ge_fifty_five_combine211
                α D hno (B 1) (B 0) (B 2) (hBdisj 1 0 (by decide)) (hBdisj 1 2 (by decide))
                (hBdisj 0 2 (by decide)) c hc hcd C1 hC1 hC1c C2 hC2 hC2c
          have b0 : 21 ≤ cut 0 := h21 0 (hn2 0 (by decide))
          have b2 : 28 ≤ cut 2 := h28 2 hnp1
          omega
        · have b0 : 28 ≤ cut 0 := h28 0 hc0
          have b2 : 21 ≤ cut 2 := h21 2 (hn2 2 (by decide))
          omega
      · have hn2 : ∀ j : Fin 3, j ≠ 2 → ¬ (∃ d : Fin 2 → Finset α,
            (∀ m, d m ⊆ B j ∧ digraph_directed_cycle_on D (d m)) ∧
              Pairwise (fun a b => Disjoint (d a) (d b))) := fun j hj hp => by
          obtain ⟨d, hd, hdd⟩ := hp
          exact digraph_three_large_parts_no_four_cycles_cross_ge_fifty_five_combine22
            α D hno (B 2) (B j) (hBdisj 2 j (Ne.symm hj)) c hc hcd d hd hdd
        have hb2 : 6 ≤ cut 2 := h6 2 (hno3 2)
        by_cases hc0 : ∃ C : Finset α, C ⊆ B 0 ∧ digraph_directed_cycle_on D C
        · obtain ⟨C1, hC1, hC1c⟩ := hc0
          have hnp1 : ¬ (∃ C : Finset α, C ⊆ B 1 ∧ digraph_directed_cycle_on D C) :=
            fun hp => by
              obtain ⟨C2, hC2, hC2c⟩ := hp
              exact digraph_three_large_parts_no_four_cycles_cross_ge_fifty_five_combine211
                α D hno (B 2) (B 0) (B 1) (hBdisj 2 0 (by decide)) (hBdisj 2 1 (by decide))
                (hBdisj 0 1 (by decide)) c hc hcd C1 hC1 hC1c C2 hC2 hC2c
          have b0 : 21 ≤ cut 0 := h21 0 (hn2 0 (by decide))
          have b1 : 28 ≤ cut 1 := h28 1 hnp1
          omega
        · have b0 : 28 ≤ cut 0 := h28 0 hc0
          have b1 : 21 ≤ cut 1 := h21 1 (hn2 1 (by decide))
          omega
    · have hno2 : ∀ m : Fin 3, ¬ (∃ c : Fin 2 → Finset α,
          (∀ a, c a ⊆ B m ∧ digraph_directed_cycle_on D (c a)) ∧
            Pairwise (fun a b => Disjoint (c a) (c b))) := fun m hm => hP2 ⟨m, hm⟩
      have c0 : 21 ≤ cut 0 := h21 0 (hno2 0)
      have c1 : 21 ≤ cut 1 := h21 1 (hno2 1)
      have c2 : 21 ≤ cut 2 := h21 2 (hno2 2)
      omega
