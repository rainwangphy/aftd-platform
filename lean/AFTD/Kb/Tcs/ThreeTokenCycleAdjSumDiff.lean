import AFTD.Prelude
import AFTD.Kb.Tcs.TokenGraph

/-!
# three_token_cycle_adj_sum_diff

Topic: graphs   Node: 72645ad6677e

Provenance: helper lemma. arXiv:2611.22830 Section 5; open problem OP-2010

For any natural number n ≥ 3 and any two adjacent vertices x and y in the 3-token graph of C_n, the difference in ZMod n between the sum of elements in x and the sum of elements in y is either 1 or -1.
-/

open SimpleGraph Finset

private theorem three_token_cycle_adj_sum_diff_fin_sub_to_zmod (n : ℕ) (u v : Fin n)
    (h : ((u - v : Fin n) : ℕ) = 1) :
    (u : ZMod n) - (v : ZMod n) = 1 := by
  have h1 : (((u - v : Fin n) : ℕ) : ZMod n) = 1 := by
    rw [h, Nat.cast_one]
  have h2 : (((u - v : Fin n) : ℕ) : ZMod n) = (u : ZMod n) - (v : ZMod n) := by
    rw [Fin.sub_def]
    dsimp
    rw [ZMod.natCast_mod]
    push_cast
    have : (v.val ≤ n) := le_of_lt v.isLt
    rw [Nat.cast_sub this]
    simp only [CharP.cast_eq_zero, zero_sub]
    abel
  rw [← h2, h1]

private theorem three_token_cycle_adj_sum_diff_cycle_adj_zmod (n : ℕ) (u v : Fin n)
    (h : (cycleGraph n).Adj u v) :
    (u : ZMod n) - (v : ZMod n) = 1 ∨ (v : ZMod n) - (u : ZMod n) = 1 := by
  rw [cycleGraph_adj'] at h
  rcases h with h1 | h2
  · left; exact three_token_cycle_adj_sum_diff_fin_sub_to_zmod n u v h1
  · right; exact three_token_cycle_adj_sum_diff_fin_sub_to_zmod n v u h2

private theorem three_token_cycle_adj_sum_diff_finset_sum_sub_sum {α β : Type*} [DecidableEq α] [AddCommGroup β]
    (s t : Finset α) (f : α → β) :
    s.sum f - t.sum f = (s \ t).sum f - (t \ s).sum f := by
  have hs : s \ (s ∩ t) = s \ t := by rw [inter_comm, sdiff_inter_self_right]
  have ht : t \ (s ∩ t) = t \ s := sdiff_inter_self_right t s
  have h1 := sum_sdiff (s₁ := s ∩ t) (s₂ := s) inter_subset_left (f := f)
  have h2 := sum_sdiff (s₁ := s ∩ t) (s₂ := t) inter_subset_right (f := f)
  rw [hs] at h1
  rw [ht] at h2
  rw [← h1, ← h2]
  abel

private theorem three_token_cycle_adj_sum_diff_sdiff_cases_of_symmDiff_pair
    {α : Type*} [DecidableEq α] {s t : Finset α}
    (hcard : s.card = t.card) {u v : α} (hne : u ≠ v) (hdiff : symmDiff s t = {u, v}) :
    (s \ t = {u} ∧ t \ s = {v}) ∨ (s \ t = {v} ∧ t \ s = {u}) := by
  have h_symm : s \ t ∪ t \ s = {u, v} := by
    rw [← Finset.symmDiff_def, hdiff]
  have h_disj : Disjoint (s \ t) (t \ s) := disjoint_sdiff_sdiff
  have h_card_uv : ({u, v} : Finset α).card = 2 := card_pair hne
  have h_card_st : (s \ t).card = (t \ s).card := by
    have h1 : s.card = (s \ t).card + (s ∩ t).card := by
      rw [← card_sdiff_add_card_inter]
    have h2 : t.card = (t \ s).card + (t ∩ s).card := by
      rw [← card_sdiff_add_card_inter]
    rw [inter_comm] at h2
    omega
  have h_union_card : (s \ t ∪ t \ s).card = (s \ t).card + (t \ s).card :=
    card_union_of_disjoint h_disj
  have h_card_one : (s \ t).card = 1 := by
    rw [h_symm, h_card_uv] at h_union_card
    omega
  obtain ⟨a, ha⟩ := card_eq_one.mp h_card_one
  have ha_mem : a ∈ ({u, v} : Finset α) := by
    have : a ∈ s \ t ∪ t \ s := by
      rw [mem_union, ha, mem_singleton]
      exact Or.inl rfl
    rw [h_symm] at this
    exact this
  simp only [mem_insert, mem_singleton] at ha_mem
  have h_sub_union (x : α) : x ∈ t \ s ↔ x ∈ ({u, v} : Finset α) ∧ x ∉ s \ t := by
    have h_mem_u : x ∈ s \ t ∪ t \ s ↔ x ∈ ({u, v} : Finset α) := by rw [h_symm]
    rw [mem_union] at h_mem_u
    constructor
    · intro hx
      refine ⟨h_mem_u.mp (Or.inr hx), ?_⟩
      intro h_st
      exact (disjoint_left.mp h_disj h_st) hx
    · intro ⟨h_uv, h_not_st⟩
      rcases h_mem_u.mpr h_uv with h1 | h2
      · exact (h_not_st h1).elim
      · exact h2
  rcases ha_mem with rfl | rfl
  · left
    refine ⟨ha, ?_⟩
    ext x
    rw [h_sub_union, ha]
    simp only [mem_insert, mem_singleton]
    aesop
  · right
    refine ⟨ha, ?_⟩
    ext x
    rw [h_sub_union, ha]
    simp only [mem_insert, mem_singleton]
    aesop

/-- Adjacent 3-subsets in the token graph of C_n have coordinate sums in ZMod n differing by 1. -/
theorem three_token_cycle_adj_sum_diff (n : ℕ) (hn : 3 ≤ n)
    (x y : { s : Finset (Fin n) // s.card = 3 })
    (h : (token_graph (SimpleGraph.cycleGraph n) 3).Adj x y) :
    let sx : ZMod n := x.val.sum (fun i => (i : ZMod n))
    let sy : ZMod n := y.val.sum (fun i => (i : ZMod n))
    sx - sy = 1 ∨ sy - sx = 1 := by
  intro sx sy
  obtain ⟨u, v, hadj, hdiff⟩ := h
  have hne : u ≠ v := hadj.ne
  have hcard : x.val.card = y.val.card := by rw [x.2, y.2]
  have hcases := three_token_cycle_adj_sum_diff_sdiff_cases_of_symmDiff_pair hcard hne hdiff
  have hsum : sx - sy = (x.val \ y.val).sum (fun i : Fin n => (i : ZMod n)) -
                        (y.val \ x.val).sum (fun i : Fin n => (i : ZMod n)) :=
    three_token_cycle_adj_sum_diff_finset_sum_sub_sum x.val y.val (fun i : Fin n => (i : ZMod n))
  have hadj_zmod := three_token_cycle_adj_sum_diff_cycle_adj_zmod n u v hadj
  rcases hcases with ⟨hxy, hyx⟩ | ⟨hxy, hyx⟩
  · rw [hxy, hyx, sum_singleton, sum_singleton] at hsum
    rcases hadj_zmod with h1 | h2
    · left; rw [hsum, h1]
    · right
      have : sy - sx = -(sx - sy) := (neg_sub sx sy).symm
      rw [this, hsum, neg_sub, h2]
  · rw [hxy, hyx, sum_singleton, sum_singleton] at hsum
    rcases hadj_zmod with h1 | h2
    · right
      have : sy - sx = -(sx - sy) := (neg_sub sx sy).symm
      rw [this, hsum, neg_sub, h1]
    · left; rw [hsum, h2]
