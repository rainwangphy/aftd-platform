import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphDirectedCycleOn

/-!
# digraph_low_cut_contains_cycle

Topic: graphs   Node: 71b6fb808225

Provenance: helper lemma. Cut-count reduction for the minimum-counterexample route to OP-110.

In a finite loopless digraph with minimum outdegree at least r, a vertex set of at least r vertices contains a directed cycle if fewer than r(r+1)/2 arcs leave it.
-/

/-- The sum of `r - j` over `j : Fin r` is `r * (r + 1) / 2`. -/
theorem digraph_low_cut_contains_cycle_sum_fin (r : ℕ) :
    (∑ j : Fin r, (r - (j:ℕ))) = r * (r + 1) / 2 := by
  have h1 : (∑ j : Fin r, (r - (j:ℕ))) = ∑ k ∈ Finset.range r, (r - k) := by
    rw [Finset.sum_fin_eq_sum_range]
    refine Finset.sum_congr rfl ?_
    intro k hk
    simp only [Finset.mem_range] at hk
    simp [hk]
  rw [h1]
  have h2 : ∑ k ∈ Finset.range r, (r - k) = ∑ k ∈ Finset.range r, (k + 1) := by
    have := Finset.sum_range_reflect (fun k => k + 1) r
    rw [← this]
    refine Finset.sum_congr rfl ?_
    intro k hk
    simp only [Finset.mem_range] at hk
    omega
  rw [h2]
  rw [Finset.sum_add_distrib]
  simp only [Finset.sum_const_nat (m := 1) (fun x _ => rfl), Finset.card_range, mul_one]
  rw [Finset.sum_range_id]
  apply Nat.eq_div_of_mul_eq_right (c := 2) (by norm_num)
  have h2even : r * (r - 1) = 2 * (r * (r - 1) / 2) := by
    rw [Nat.mul_comm 2, Nat.div_two_mul_two_of_even (Nat.even_mul_pred_self r)]
  have key : r * (r - 1) + 2 * r = r * (r + 1) := by
    cases r with
    | zero => simp
    | succ n =>
        have hsub : n + 1 - 1 = n := by omega
        rw [hsub]
        ring
  rw [Nat.mul_add, ← h2even]
  exact key

/-- A finite nonempty vertex set in which every vertex has an out-neighbour inside it
contains a directed cycle. -/
theorem digraph_low_cut_contains_cycle_outdeg_cycle
    (α : Type) [Fintype α] [DecidableEq α]
    (D : Digraph α) [DecidableRel D.Adj]
    (hloop : ∀ v, ¬ D.Adj v v) (X : Finset α)
    (hne : X.Nonempty) (hout : ∀ v ∈ X, ∃ w ∈ X, D.Adj v w) :
    ∃ C : Finset α, C ⊆ X ∧ digraph_directed_cycle_on D C := by
  let S := {x : α // x ∈ X}
  have hS : ∀ s : S, ∃ t : S, D.Adj s.1 t.1 := by
    intro s; obtain ⟨w, hw, hadj⟩ := hout s.1 s.2; exact ⟨⟨w, hw⟩, hadj⟩
  let step : S → S := fun s => (hS s).choose
  have hstep : ∀ s : S, D.Adj s.1 (step s).1 := fun s => (hS s).choose_spec
  obtain ⟨v0, hv0⟩ := hne
  let s0 : S := ⟨v0, hv0⟩
  let x : ℕ → S := fun t => step^[t] s0
  have hxstep : ∀ t, x (t + 1) = step (x t) := fun t => Function.iterate_succ_apply' step t s0
  have hxadj : ∀ t, D.Adj (x t).1 (x (t + 1)).1 := by
    intro t; rw [hxstep]; exact hstep (x t)
  have hninj : ¬ Function.Injective x := not_injective_infinite_finite x
  have hex : ∃ n, ∃ m < n, x m = x n := by
    by_contra h; apply hninj; intro u v huv
    rcases lt_trichotomy u v with hlt | heq | hgt
    · exfalso
      have : ¬ ∃ m < v, x m = x v := fun ⟨m, hm, hx⟩ => h ⟨v, m, hm, hx⟩
      push Not at this; exact this u hlt huv
    · exact heq
    · exfalso
      have : ¬ ∃ m < u, x m = x u := fun ⟨m, hm, hx⟩ => h ⟨u, m, hm, hx⟩
      push Not at this; exact this v hgt huv.symm
  classical
  let n := Nat.find hex
  obtain ⟨m, hmn, hxmn⟩ := Nat.find_spec hex
  have hmin : ∀ t < n, ¬ ∃ s < t, x s = x t := fun t ht => Nat.find_min hex ht
  have hinj : ∀ i < n, ∀ j < n, x i = x j → i = j := by
    intro i hi j hj hij
    rcases lt_trichotomy i j with hlt | heq | hgt
    · exfalso; exact hmin j hj ⟨i, hlt, hij⟩
    · exact heq
    · exfalso; exact hmin i hi ⟨j, hgt, hij.symm⟩
  have hk : n - m ≠ 0 := by omega
  have hk2 : 2 ≤ n - m := by
    by_contra! h
    have hnm1 : n = m + 1 := by omega
    have hx1 : x (m + 1) = x m := by rw [← hnm1, hxmn.symm]
    have hadj := hxadj m; rw [hx1] at hadj; exact hloop (x m).1 hadj
  let k := n - m
  let c : ℕ → α := fun i => (x (m + i)).1
  let l : List α := (List.range k).map c
  have hlen : l.length = k := by simp [l]
  have hnodup : l.Nodup := by
    refine (List.nodup_map_iff_inj_on List.nodup_range).mpr ?_
    intro i hi j hj hij
    simp only [List.mem_range] at hi hj
    have heq : x (m + i) = x (m + j) := Subtype.ext hij
    have hi' : m + i < n := by omega
    have hj' : m + j < n := by omega
    have : m + i = m + j := hinj (m + i) hi' (m + j) hj' heq
    omega
  have hchain : l.IsChain D.Adj := by
    rw [List.isChain_iff_getElem]
    intro i hi
    have hik : i + 1 < k := by simpa [hlen] using hi
    have h1 : l[i] = c i := by simp [l]
    have h2 : l[i + 1] = c (i + 1) := by simp [l]
    rw [h1, h2]; dsimp [c]
    have hrel : m + (i + 1) = (m + i) + 1 := by omega
    rw [hrel]; exact hxadj (m + i)
  have hhead : l.head? = some (c 0) := by
    rw [List.head?_map, List.head?_range]
    have hk0 : k ≠ 0 := by omega
    simp [hk0]
  have hlast : l.getLast? = some (c (k - 1)) := by
    rw [List.getLast?_map, List.getLast?_range]
    have hk0 : k ≠ 0 := by omega
    simp [hk0]
  have hadj_last_head : D.Adj (c (k - 1)) (c 0) := by
    have h1 : m + (k - 1) = n - 1 := by omega
    have h2 : m + 0 = m := by omega
    show D.Adj (x (m + (k - 1))).1 (x (m + 0)).1
    rw [h1, h2, hxmn]
    have hn : (n - 1) + 1 = n := by omega
    show D.Adj (x (n - 1)).1 (x n).1
    rw [← hn]; exact hxadj (n - 1)
  refine ⟨l.toFinset, ?_, ⟨l, hnodup, by rw [hlen]; exact hk2, rfl, hchain, ⟨c 0, c (k - 1), hhead, hlast, hadj_last_head⟩⟩⟩
  intro v hv
  rw [List.mem_toFinset] at hv
  rcases List.mem_map.mp hv with ⟨i, hi, rfl⟩
  exact (x (m + i)).2

/-- A finite nonempty vertex set containing no directed cycle has a vertex with no
out-neighbour inside it. -/
theorem digraph_low_cut_contains_cycle_sink
    (α : Type) [Fintype α] [DecidableEq α]
    (D : Digraph α) [DecidableRel D.Adj]
    (hloop : ∀ v, ¬ D.Adj v v) (X : Finset α) (hne : X.Nonempty)
    (hac : ∀ C, C ⊆ X → ¬ digraph_directed_cycle_on D C) :
    ∃ s ∈ X, ∀ w ∈ X, ¬ D.Adj s w := by
  by_contra h
  push Not at h
  obtain ⟨C, hCX, hcyc⟩ := digraph_low_cut_contains_cycle_outdeg_cycle α D hloop X hne h
  exact hac C hCX hcyc

/-- From a cycle-free vertex set of size at least `r` one can peel `r` vertices so that the
`j`-th peeled vertex has at most `j` out-neighbours inside the set. -/
theorem digraph_low_cut_contains_cycle_peel
    (α : Type) [Fintype α] [DecidableEq α]
    (D : Digraph α) [DecidableRel D.Adj]
    (hloop : ∀ v, ¬ D.Adj v v) :
    ∀ (r : ℕ) (X : Finset α),
      (∀ C, C ⊆ X → ¬ digraph_directed_cycle_on D C) → r ≤ X.card →
      ∃ s : Fin r → α, Function.Injective s ∧ (∀ j, s j ∈ X) ∧
        ∀ j, (X.filter (fun w => D.Adj (s j) w)).card ≤ (j : ℕ) := by
  intro r
  induction r with
  | zero =>
      intro X hac hr
      exact ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ r ih =>
      intro X hac hr
      have hne : X.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨s0, hs0X, hsink⟩ := digraph_low_cut_contains_cycle_sink α D hloop X hne hac
      have hac' : ∀ C, C ⊆ X.erase s0 → ¬ digraph_directed_cycle_on D C :=
        fun C hC => hac C (hC.trans (Finset.erase_subset s0 X))
      have hr' : r ≤ (X.erase s0).card := by
        rw [Finset.card_erase_of_mem hs0X]; omega
      obtain ⟨s', hinj', hmem', hbound'⟩ := ih (X.erase s0) hac' hr'
      let s : Fin (r+1) → α := Fin.cons s0 s'
      refine ⟨s, ?_, ?_, ?_⟩
      · show Function.Injective (Fin.cons s0 s')
        apply Fin.cons_injective_of_injective
        · rintro ⟨i, hi⟩
          exact (Finset.mem_erase.mp (hmem' i)).1 hi
        · exact hinj'
      · intro j
        induction j using Fin.cases with
        | zero => simpa only [s, Fin.cons_zero] using hs0X
        | succ i =>
            simpa only [s, Fin.cons_succ] using (Finset.mem_erase.mp (hmem' i)).2
      · intro j
        induction j using Fin.cases with
        | zero =>
            have hempty : X.filter (fun w => D.Adj (s 0) w) = ∅ := by
              simp only [s, Fin.cons_zero]
              rw [Finset.filter_eq_empty_iff]
              intro w hw
              exact hsink w hw
            rw [hempty]
            simp
        | succ i =>
            simp only [s, Fin.cons_succ]
            have hsub : X.filter (fun w => D.Adj (s' i) w)
                ⊆ (X.erase s0).filter (fun w => D.Adj (s' i) w) ∪ ({s0} : Finset α) := by
              intro w hw
              simp only [Finset.mem_filter] at hw
              rw [Finset.mem_union]
              by_cases hw0 : w = s0
              · right; simp [hw0]
              · left
                simp only [Finset.mem_filter, Finset.mem_erase]
                exact ⟨⟨hw0, hw.1⟩, hw.2⟩
            have h1 := Finset.card_le_card hsub
            have h2 := Finset.card_union_le ((X.erase s0).filter (fun w => D.Adj (s' i) w)) ({s0} : Finset α)
            have h3 := hbound' i
            rw [Finset.card_singleton] at h2
            simp only [Fin.val_succ]
            omega

theorem digraph_low_cut_contains_cycle (α : Type) [Fintype α] [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj] (r : ℕ) (hloop : ∀ v, ¬ D.Adj v v) (hdeg : ∀ v, r ≤ (Finset.univ.filter fun w => D.Adj v w).card) (B : Finset α) (hB : r ≤ B.card) (hcut : (∑ v ∈ B, (Bᶜ.filter fun w => D.Adj v w).card) < r * (r + 1) / 2) : ∃ C : Finset α, C ⊆ B ∧ digraph_directed_cycle_on D C := by
  by_contra hno
  push Not at hno
  obtain ⟨s, hinj, hmem, hbound⟩ :=
    digraph_low_cut_contains_cycle_peel α D hloop r B hno hB
  have hterm : ∀ j : Fin r, r - (j:ℕ) ≤ (Bᶜ.filter fun w => D.Adj (s j) w).card := by
    intro j
    have hout : r ≤ (Finset.univ.filter (fun w => D.Adj (s j) w)).card := hdeg (s j)
    have hint : (B.filter (fun w => D.Adj (s j) w)).card ≤ (j:ℕ) := hbound j
    have hdisj : Disjoint (B.filter (fun w => D.Adj (s j) w)) (Bᶜ.filter (fun w => D.Adj (s j) w)) := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [Finset.mem_filter] at hx hx'
      exact (Finset.mem_compl.mp hx'.1) hx.1
    have hunion : B.filter (fun w => D.Adj (s j) w) ∪ Bᶜ.filter (fun w => D.Adj (s j) w)
        = Finset.univ.filter (fun w => D.Adj (s j) w) := by
      rw [← Finset.filter_union, Finset.union_compl]
    have hpart : (Finset.univ.filter (fun w => D.Adj (s j) w)).card
        = (B.filter (fun w => D.Adj (s j) w)).card + (Bᶜ.filter (fun w => D.Adj (s j) w)).card := by
      rw [← hunion, Finset.card_union_of_disjoint hdisj]
    omega
  have hsum_ge : r * (r + 1) / 2 ≤ ∑ j : Fin r, (Bᶜ.filter fun w => D.Adj (s j) w).card := by
    have h1 : ∑ j : Fin r, (r - (j:ℕ)) ≤ ∑ j : Fin r, (Bᶜ.filter fun w => D.Adj (s j) w).card :=
      Finset.sum_le_sum (fun j _ => hterm j)
    rwa [digraph_low_cut_contains_cycle_sum_fin r] at h1
  have hsum_le : ∑ j : Fin r, (Bᶜ.filter fun w => D.Adj (s j) w).card
      ≤ ∑ v ∈ B, (Bᶜ.filter fun w => D.Adj v w).card := by
    have himg : ∑ j : Fin r, (Bᶜ.filter fun w => D.Adj (s j) w).card
        = ∑ v ∈ (Finset.univ.image s), (Bᶜ.filter fun w => D.Adj v w).card := by
      rw [Finset.sum_image (f := fun v => (Bᶜ.filter fun w => D.Adj v w).card)
            (g := s) (s := Finset.univ) (fun i _ j _ h => hinj h)]
    rw [himg]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.image_subset_iff.mpr (fun j _ => hmem j))
      (fun v _ _ => Nat.zero_le _)
  have hfinal : r * (r + 1) / 2 ≤ ∑ v ∈ B, (Bᶜ.filter fun w => D.Adj v w).card :=
    le_trans hsum_ge hsum_le
  exact absurd hcut (not_lt.mpr hfinal)
