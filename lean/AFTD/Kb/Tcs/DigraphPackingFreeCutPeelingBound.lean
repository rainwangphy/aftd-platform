import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphDirectedCycleOn

/-!
# digraph_packing_free_cut_peeling_bound

Topic: graphs   Node: e51925a35eb7

Provenance: helper lemma. Peeling reduction for the minimum-counterexample campaign route to OP-110; experiments 12598 and 12602 check the resulting degree and partition arithmetic.

If a set of at least r−m+1 vertices contains no q disjoint directed cycles, while every nonempty induced digraph of minimum outdegree m contains q cycles and all vertices of the set have global outdegree at least r, at least (r−m+1)(r−m+2)/2 arcs leave the set.
-/

private theorem in516_triangular_sum (r : ℕ) :
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

private theorem in516_peel (α : Type) [Fintype α] [DecidableEq α]
    (D : Digraph α) [DecidableRel D.Adj] (m : ℕ) :
    ∀ (n : ℕ) (X : Finset α),
      (∀ T ⊆ X, T.Nonempty → ∃ v ∈ T, (T.filter fun w => D.Adj v w).card < m) →
      n ≤ X.card →
      ∃ s : Fin n → α, Function.Injective s ∧ (∀ j, s j ∈ X) ∧
        ∀ j, (X.filter fun w => D.Adj (s j) w).card < m + (j : ℕ) := by
  intro n
  induction n with
  | zero =>
      intro X h hr
      exact ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
  | succ n ih =>
      intro X h hr
      have hne : X.Nonempty := Finset.card_pos.mp (by omega)
      obtain ⟨s0, hs0X, hsink⟩ := h X (Finset.Subset.refl X) hne
      have h' : ∀ T ⊆ X.erase s0, T.Nonempty → ∃ v ∈ T, (T.filter fun w => D.Adj v w).card < m :=
        fun T hT hne => h T (hT.trans (Finset.erase_subset s0 X)) hne
      have hr' : n ≤ (X.erase s0).card := by
        rw [Finset.card_erase_of_mem hs0X]; omega
      obtain ⟨s', hinj', hmem', hbound'⟩ := ih (X.erase s0) h' hr'
      let s : Fin (n+1) → α := Fin.cons s0 s'
      refine ⟨s, ?_, ?_, ?_⟩
      · show Function.Injective (Fin.cons s0 s')
        apply Fin.cons_injective_of_injective
        · rintro ⟨i, hi⟩
          exact (Finset.mem_erase.mp (hmem' i)).1 hi
        · exact hinj'
      · intro j
        induction j using Fin.cases with
        | zero => simpa only [s, Fin.cons_zero] using hs0X
        | succ i => simpa only [s, Fin.cons_succ] using (Finset.mem_erase.mp (hmem' i)).2
      · intro j
        induction j using Fin.cases with
        | zero => simpa only [s, Fin.cons_zero, Fin.val_zero, Nat.add_zero] using hsink
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

theorem digraph_packing_free_cut_peeling_bound
    (α : Type) [Fintype α] [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj]
    (r m q : ℕ) (hm : m ≤ r) (B : Finset α) (hB : r - m + 1 ≤ B.card)
    (hdeg : ∀ v ∈ B, r ≤ (Finset.univ.filter fun w => D.Adj v w).card)
    (hcriterion : ∀ T : Finset α, T.Nonempty →
      (∀ v ∈ T, m ≤ (T.filter fun w => D.Adj v w).card) →
      ∃ c : Fin q → Finset α, (∀ i, c i ⊆ T ∧ digraph_directed_cycle_on D (c i)) ∧
        Pairwise (fun i j => Disjoint (c i) (c j)))
    (hno : ¬ ∃ c : Fin q → Finset α,
      (∀ i, c i ⊆ B ∧ digraph_directed_cycle_on D (c i)) ∧
        Pairwise (fun i j => Disjoint (c i) (c j))) :
    (r - m + 1) * (r - m + 2) / 2 ≤
      ∑ v ∈ B, (Bᶜ.filter fun w => D.Adj v w).card := by
  classical
  have hsmall : ∀ T ⊆ B, T.Nonempty → ∃ v ∈ T, (T.filter fun w => D.Adj v w).card < m := by
    intro T hTB hT
    by_contra hn
    have hd : ∀ v ∈ T, m ≤ (T.filter fun w => D.Adj v w).card := by
      intro v hv
      by_contra hh
      exact hn ⟨v, hv, by omega⟩
    obtain ⟨c, hc, hp⟩ := hcriterion T hT hd
    exact hno ⟨c, fun i => ⟨(hc i).1.trans hTB, (hc i).2⟩, hp⟩
  let n := r - m + 1
  obtain ⟨s, hinj, hmem, hbound⟩ := in516_peel α D m n B hsmall hB
  have hterm : ∀ j : Fin n, n - (j:ℕ) ≤ (Bᶜ.filter fun w => D.Adj (s j) w).card := by
    intro j
    have hout := hdeg (s j) (hmem j)
    have hint := hbound j
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
    dsimp [n] at *
    omega
  have hsum_ge : n * (n + 1) / 2 ≤ ∑ j : Fin n, (Bᶜ.filter fun w => D.Adj (s j) w).card := by
    have h1 : ∑ j : Fin n, (n - (j:ℕ)) ≤ ∑ j : Fin n, (Bᶜ.filter fun w => D.Adj (s j) w).card :=
      Finset.sum_le_sum (fun j _ => hterm j)
    rwa [in516_triangular_sum n] at h1
  have hsum_le : ∑ j : Fin n, (Bᶜ.filter fun w => D.Adj (s j) w).card
      ≤ ∑ v ∈ B, (Bᶜ.filter fun w => D.Adj v w).card := by
    have himg : ∑ j : Fin n, (Bᶜ.filter fun w => D.Adj (s j) w).card
        = ∑ v ∈ (Finset.univ.image s), (Bᶜ.filter fun w => D.Adj v w).card := by
      rw [Finset.sum_image (f := fun v => (Bᶜ.filter fun w => D.Adj v w).card)
            (g := s) (s := Finset.univ) (fun i _ j _ h => hinj h)]
    rw [himg]
    exact Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.image_subset_iff.mpr (fun j _ => hmem j))
      (fun v _ _ => Nat.zero_le _)
  have hfinal := le_trans hsum_ge hsum_le
  dsimp [n] at hfinal
  convert hfinal using 1
