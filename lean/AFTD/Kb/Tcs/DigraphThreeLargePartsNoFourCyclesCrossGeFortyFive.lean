import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphDirectedCycleOn
import AFTD.Kb.Tcs.DigraphPackingFreeCutPeelingBound

/-!
# digraph_three_large_parts_no_four_cycles_cross_ge_forty_five

Topic: graphs   Node: 01651dba94eb

Provenance: helper lemma. Partition peeling reduction for OP-110; experiment 12602 checks the cycle-allocation arithmetic.

If a finite digraph of minimum outdegree seven has no four disjoint directed cycles and its vertices are partitioned into three parts each of size at least seven, then at least 45 arcs cross between parts, assuming the displayed one-, two- and three-cycle criteria.
-/

def digraph_three_large_parts_no_four_cycles_cross_ge_forty_five_has_pack1 {α : Type} [DecidableEq α] (D : Digraph α) (S : Finset α) : Prop :=
  ∃ C : Finset α, C ⊆ S ∧ digraph_directed_cycle_on D C

def digraph_three_large_parts_no_four_cycles_cross_ge_forty_five_has_pack2 {α : Type} [DecidableEq α] (D : Digraph α) (S : Finset α) : Prop :=
  ∃ c : Fin 2 → Finset α, (∀ m, c m ⊆ S ∧ digraph_directed_cycle_on D (c m)) ∧
    Pairwise (fun a b => Disjoint (c a) (c b))

def digraph_three_large_parts_no_four_cycles_cross_ge_forty_five_has_pack3 {α : Type} [DecidableEq α] (D : Digraph α) (S : Finset α) : Prop :=
  ∃ c : Fin 3 → Finset α, (∀ m, c m ⊆ S ∧ digraph_directed_cycle_on D (c m)) ∧
    Pairwise (fun a b => Disjoint (c a) (c b))

lemma digraph_three_large_parts_no_four_cycles_cross_ge_forty_five_col_disjoint {α : Type} [Fintype α] (col : α → Fin 3) {i j : Fin 3} (hij : i ≠ j) :
    Disjoint (Finset.univ.filter fun v => col v = i) (Finset.univ.filter fun v => col v = j) := by
  rw [Finset.disjoint_filter]
  intro x _ hi hj
  exact hij (hi.symm.trans hj)

lemma digraph_three_large_parts_no_four_cycles_cross_ge_forty_five_no_two_two {α : Type} [Fintype α] [DecidableEq α] (D : Digraph α) (col : α → Fin 3)
    (hno : ¬ ∃ c : Fin 4 → Finset α, (∀ i, digraph_directed_cycle_on D (c i)) ∧
      Pairwise (fun i j => Disjoint (c i) (c j)))
    {i j : Fin 3} (hij : i ≠ j)
    (hA : digraph_three_large_parts_no_four_cycles_cross_ge_forty_five_has_pack2 D (Finset.univ.filter fun v => col v = i))
    (hB : digraph_three_large_parts_no_four_cycles_cross_ge_forty_five_has_pack2 D (Finset.univ.filter fun v => col v = j)) :
    False := by
  obtain ⟨cA, hcA, hpA⟩ := hA
  obtain ⟨cB, hcB, hpB⟩ := hB
  let c : Fin 4 → Finset α := ![cA 0, cA 1, cB 0, cB 1]
  apply hno
  refine ⟨c, ?_, ?_⟩
  · intro k; fin_cases k
    · exact (hcA 0).2
    · exact (hcA 1).2
    · exact (hcB 0).2
    · exact (hcB 1).2
  · have hdAB : ∀ a b, Disjoint (cA a) (cB b) := fun a b =>
      Disjoint.mono (hcA a).1 (hcB b).1 (digraph_three_large_parts_no_four_cycles_cross_ge_forty_five_col_disjoint col hij)
    have h01 : Disjoint (cA 0) (cA 1) := hpA (by decide)
    have h23 : Disjoint (cB 0) (cB 1) := hpB (by decide)
    have h02 := hdAB 0 0
    have h03 := hdAB 0 1
    have h12 := hdAB 1 0
    have h13 := hdAB 1 1
    intro a b hab
    fin_cases a <;> fin_cases b <;> try contradiction
    all_goals
      first
      | exact h01 | exact h01.symm
      | exact h02 | exact h02.symm
      | exact h03 | exact h03.symm
      | exact h12 | exact h12.symm
      | exact h13 | exact h13.symm
      | exact h23 | exact h23.symm

lemma digraph_three_large_parts_no_four_cycles_cross_ge_forty_five_no_three_one {α : Type} [Fintype α] [DecidableEq α] (D : Digraph α) (col : α → Fin 3)
    (hno : ¬ ∃ c : Fin 4 → Finset α, (∀ i, digraph_directed_cycle_on D (c i)) ∧
      Pairwise (fun i j => Disjoint (c i) (c j)))
    {i j : Fin 3} (hij : i ≠ j)
    (hA : digraph_three_large_parts_no_four_cycles_cross_ge_forty_five_has_pack3 D (Finset.univ.filter fun v => col v = i))
    (hB : digraph_three_large_parts_no_four_cycles_cross_ge_forty_five_has_pack1 D (Finset.univ.filter fun v => col v = j)) :
    False := by
  obtain ⟨cA, hcA, hpA⟩ := hA
  obtain ⟨C, hC1, hC2⟩ := hB
  let c : Fin 4 → Finset α := ![cA 0, cA 1, cA 2, C]
  apply hno
  refine ⟨c, ?_, ?_⟩
  · intro k; fin_cases k
    · exact (hcA 0).2
    · exact (hcA 1).2
    · exact (hcA 2).2
    · exact hC2
  · have hdAC : ∀ a, Disjoint (cA a) C := fun a =>
      Disjoint.mono (hcA a).1 hC1 (digraph_three_large_parts_no_four_cycles_cross_ge_forty_five_col_disjoint col hij)
    have h01 : Disjoint (cA 0) (cA 1) := hpA (by decide)
    have h02 : Disjoint (cA 0) (cA 2) := hpA (by decide)
    have h12 : Disjoint (cA 1) (cA 2) := hpA (by decide)
    have h03 := hdAC 0
    have h13 := hdAC 1
    have h23 := hdAC 2
    intro a b hab
    fin_cases a <;> fin_cases b <;> try contradiction
    all_goals
      first
      | exact h01 | exact h01.symm
      | exact h02 | exact h02.symm
      | exact h03 | exact h03.symm
      | exact h12 | exact h12.symm
      | exact h13 | exact h13.symm
      | exact h23 | exact h23.symm

lemma digraph_three_large_parts_no_four_cycles_cross_ge_forty_five_no_two_one_one {α : Type} [Fintype α] [DecidableEq α] (D : Digraph α) (col : α → Fin 3)
    (hno : ¬ ∃ c : Fin 4 → Finset α, (∀ i, digraph_directed_cycle_on D (c i)) ∧
      Pairwise (fun i j => Disjoint (c i) (c j)))
    {i j k : Fin 3} (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k)
    (hA : digraph_three_large_parts_no_four_cycles_cross_ge_forty_five_has_pack2 D (Finset.univ.filter fun v => col v = i))
    (hB : digraph_three_large_parts_no_four_cycles_cross_ge_forty_five_has_pack1 D (Finset.univ.filter fun v => col v = j))
    (hC : digraph_three_large_parts_no_four_cycles_cross_ge_forty_five_has_pack1 D (Finset.univ.filter fun v => col v = k)) :
    False := by
  obtain ⟨cA, hcA, hpA⟩ := hA
  obtain ⟨cB, hcB1, hcB2⟩ := hB
  obtain ⟨cC, hcC1, hcC2⟩ := hC
  let c : Fin 4 → Finset α := ![cA 0, cA 1, cB, cC]
  apply hno
  refine ⟨c, ?_, ?_⟩
  · intro m; fin_cases m
    · exact (hcA 0).2
    · exact (hcA 1).2
    · exact hcB2
    · exact hcC2
  · have hdAB : ∀ a, Disjoint (cA a) cB := fun a =>
      Disjoint.mono (hcA a).1 hcB1 (digraph_three_large_parts_no_four_cycles_cross_ge_forty_five_col_disjoint col hij)
    have hdAC : ∀ a, Disjoint (cA a) cC := fun a =>
      Disjoint.mono (hcA a).1 hcC1 (digraph_three_large_parts_no_four_cycles_cross_ge_forty_five_col_disjoint col hik)
    have hdBC : Disjoint cB cC :=
      Disjoint.mono hcB1 hcC1 (digraph_three_large_parts_no_four_cycles_cross_ge_forty_five_col_disjoint col hjk)
    have h01 : Disjoint (cA 0) (cA 1) := hpA (by decide)
    have h02 := hdAB 0
    have h03 := hdAC 0
    have h12 := hdAB 1
    have h13 := hdAC 1
    have h23 := hdBC
    intro a b hab
    fin_cases a <;> fin_cases b <;> try contradiction
    all_goals
      first
      | exact h01 | exact h01.symm
      | exact h02 | exact h02.symm
      | exact h03 | exact h03.symm
      | exact h12 | exact h12.symm
      | exact h13 | exact h13.symm
      | exact h23 | exact h23.symm

lemma digraph_three_large_parts_no_four_cycles_cross_ge_forty_five_cut_sum_of_two
    (α : Type) [Fintype α] [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj]
    (col : α → Fin 3)
    (hsize : ∀ i, 7 ≤ (Finset.univ.filter fun v => col v = i).card)
    (hdeg : ∀ v, 7 ≤ (Finset.univ.filter fun w => D.Adj v w).card)
    (hone : ∀ T : Finset α, T.Nonempty →
      (∀ v ∈ T, 1 ≤ (T.filter fun w => D.Adj v w).card) →
      ∃ C : Finset α, C ⊆ T ∧ digraph_directed_cycle_on D C)
    (htwo : ∀ T : Finset α, T.Nonempty →
      (∀ v ∈ T, 3 ≤ (T.filter fun w => D.Adj v w).card) →
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
    45 ≤ ∑ v ∈ (Finset.univ.filter fun v => col v = i), ((Finset.univ.filter fun v => col v = i)ᶜ.filter fun w => D.Adj v w).card +
         ∑ v ∈ (Finset.univ.filter fun v => col v = j), ((Finset.univ.filter fun v => col v = j)ᶜ.filter fun w => D.Adj v w).card +
         ∑ v ∈ (Finset.univ.filter fun v => col v = k), ((Finset.univ.filter fun v => col v = k)ᶜ.filter fun w => D.Adj v w).card := by
  let B (m : Fin 3) := Finset.univ.filter fun v => col v = m
  let cut (m : Fin 3) := ∑ v ∈ B m, ((B m)ᶜ.filter fun w => D.Adj v w).card
  change 45 ≤ cut i + cut j + cut k
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
  have hcut2 : ∀ m : Fin 3, ¬ digraph_three_large_parts_no_four_cycles_cross_ge_forty_five_has_pack2 D (B m) → 15 ≤ cut m := by
    intro m hm2
    have hBm : 7 - 3 + 1 ≤ (B m).card := by dsimp [B]; have := hsize m; omega
    have hbound := digraph_packing_free_cut_peeling_bound α D 7 3 2 (by omega) (B m) hBm
      (fun v _ => hdeg v) htwo (by exact hm2)
    have hcalc : (7 - 3 + 1) * (7 - 3 + 2) / 2 = 15 := by rfl
    rwa [hcalc] at hbound
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

theorem digraph_three_large_parts_no_four_cycles_cross_ge_forty_five
    (α : Type) [Fintype α] [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj]
    (col : α → Fin 3)
    (hsize : ∀ i, 7 ≤ (Finset.univ.filter fun v => col v = i).card)
    (hdeg : ∀ v, 7 ≤ (Finset.univ.filter fun w => D.Adj v w).card)
    (hone : ∀ T : Finset α, T.Nonempty →
      (∀ v ∈ T, 1 ≤ (T.filter fun w => D.Adj v w).card) →
      ∃ C : Finset α, C ⊆ T ∧ digraph_directed_cycle_on D C)
    (htwo : ∀ T : Finset α, T.Nonempty →
      (∀ v ∈ T, 3 ≤ (T.filter fun w => D.Adj v w).card) →
      ∃ c : Fin 2 → Finset α, (∀ i, c i ⊆ T ∧ digraph_directed_cycle_on D (c i)) ∧
        Pairwise (fun i j => Disjoint (c i) (c j)))
    (hthree : ∀ T : Finset α, T.Nonempty →
      (∀ v ∈ T, 5 ≤ (T.filter fun w => D.Adj v w).card) →
      ∃ c : Fin 3 → Finset α, (∀ i, c i ⊆ T ∧ digraph_directed_cycle_on D (c i)) ∧
        Pairwise (fun i j => Disjoint (c i) (c j)))
    (hno : ¬ ∃ c : Fin 4 → Finset α,
      (∀ i, digraph_directed_cycle_on D (c i)) ∧
        Pairwise (fun i j => Disjoint (c i) (c j))) :
    45 ≤ ∑ v : α, (Finset.univ.filter fun w => col w ≠ col v ∧ D.Adj v w).card := by
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
  change 45 ≤ cut 0 + cut 1 + cut 2
  by_cases h : ∃ i : Fin 3, digraph_three_large_parts_no_four_cycles_cross_ge_forty_five_has_pack2 D (Finset.univ.filter fun v => col v = i)
  · obtain ⟨i, hi⟩ := h
    fin_cases i
    · have h0 := digraph_three_large_parts_no_four_cycles_cross_ge_forty_five_cut_sum_of_two α D col hsize hdeg hone htwo hthree hno 0 1 2
        (by decide) (by decide) (by decide) hi
      dsimp [cut]
      exact h0
    · have h1 := digraph_three_large_parts_no_four_cycles_cross_ge_forty_five_cut_sum_of_two α D col hsize hdeg hone htwo hthree hno 1 0 2
        (by decide) (by decide) (by decide) hi
      dsimp [cut] at *
      omega
    · have h2 := digraph_three_large_parts_no_four_cycles_cross_ge_forty_five_cut_sum_of_two α D col hsize hdeg hone htwo hthree hno 2 0 1
        (by decide) (by decide) (by decide) hi
      dsimp [cut] at *
      omega
  · have hnot : ∀ m : Fin 3, ¬ digraph_three_large_parts_no_four_cycles_cross_ge_forty_five_has_pack2 D (Finset.univ.filter fun v => col v = m) := by
      intro m hm; exact h ⟨m, hm⟩
    have hcut2 : ∀ m : Fin 3, 15 ≤ cut m := by
      intro m
      have hm2 := hnot m
      have hBm : 7 - 3 + 1 ≤ (Finset.univ.filter fun v => col v = m).card := by
        have := hsize m; omega
      have hbound := digraph_packing_free_cut_peeling_bound α D 7 3 2 (by omega)
        (Finset.univ.filter fun v => col v = m) hBm (fun v _ => hdeg v) htwo (by exact hm2)
      have hcalc : (7 - 3 + 1) * (7 - 3 + 2) / 2 = 15 := by rfl
      rwa [hcalc] at hbound
    have c0 := hcut2 0
    have c1 := hcut2 1
    have c2 := hcut2 2
    omega
