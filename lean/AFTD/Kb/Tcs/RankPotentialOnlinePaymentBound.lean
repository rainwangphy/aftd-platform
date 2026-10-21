import AFTD.Prelude
import AFTD.Kb.Tcs.FifoQueue
import AFTD.Kb.Tcs.FifoRank
import AFTD.Kb.Tcs.RankPotential
import AFTD.Kb.Tcs.FifoFetch

/-!
# rank_potential_online_payment_bound

Topic: online_algorithms   Node: 91a5b2d11afd

Provenance: formalization of a published result. Source: arXiv:2610.18767 Lemma 3.3(iii)

For any type α with decidable equality, any k ≥ 1, any FIFO queue q of capacity k, any offline cache cOpt of cardinality k, and any page v ∉ q.pages: if v ∈ cOpt then the integer change in rank potential after fetching v, (rank_potential (fifo_fetch hk q v hv) cOpt : ℤ) - (rank_potential q cOpt : ℤ), is at most -1; and unconditionally, this rank potential change is at most k.
-/

lemma rank_potential_online_payment_bound_fetch_pages_eq {α : Type*} [DecidableEq α] {k : ℕ} (hk : 1 ≤ k) (q : FifoQueue α k) (v : α) (hv : v ∉ q.pages) :
    ∃ head tail, q.pages = head :: tail ∧ (fifo_fetch hk q v hv).pages = tail ++ [v] ∧ tail.length + 1 = k ∧ head ∉ tail := by
  rcases q with ⟨_ | ⟨head, tail⟩, hlen, hnodup⟩
  · simp at hlen; omega
  · refine ⟨head, tail, rfl, rfl, ?_, ?_⟩
    · simp at hlen; exact hlen
    · rw [List.nodup_cons] at hnodup; exact hnodup.1

lemma rank_potential_online_payment_bound_fetch_v {α : Type*} [DecidableEq α] {k : ℕ} (hk : 1 ≤ k) (q : FifoQueue α k) (v : α) (hv : v ∉ q.pages) :
    fifo_rank (fifo_fetch hk q v hv) v = k := by
  obtain ⟨head, tail, hq, hq', hlen, hhd⟩ := rank_potential_online_payment_bound_fetch_pages_eq hk q v hv
  unfold fifo_rank
  have hv_mem : v ∈ (fifo_fetch hk q v hv).pages := by
    rw [hq']
    exact List.mem_append_right tail (List.mem_singleton.mpr rfl)
  rw [if_pos hv_mem]
  rw [hq']
  have hv_not_tail : v ∉ tail := by
    intro h
    have : v ∈ q.pages := by rw [hq]; exact List.mem_cons_of_mem head h
    exact hv this
  rw [List.idxOf_append_of_notMem hv_not_tail]
  have : List.idxOf v [v] = 0 := List.idxOf_cons_eq [] rfl
  rw [this]
  omega

lemma rank_potential_online_payment_bound_fetch_old {α : Type*} [DecidableEq α] {k : ℕ} (hk : 1 ≤ k) (q : FifoQueue α k) (v : α) (hv : v ∉ q.pages)
    (x : α) (hx : x ∈ q.pages) :
    fifo_rank (fifo_fetch hk q v hv) x = fifo_rank q x - 1 := by
  obtain ⟨head, tail, hq, hq', hlen, hhd⟩ := rank_potential_online_payment_bound_fetch_pages_eq hk q v hv
  have hx_cases : x = head ∨ x ∈ tail := by
    rw [hq] at hx
    cases hx with
    | head => left; rfl
    | tail _ h => right; exact h
  rcases hx_cases with rfl | hx_tail
  · have h_not_in : x ∉ (fifo_fetch hk q v hv).pages := by
      rw [hq']
      simp only [List.mem_append, List.mem_singleton, not_or]
      refine ⟨hhd, ?_⟩
      rintro rfl
      exact hv hx
    unfold fifo_rank
    rw [if_neg h_not_in]
    rw [if_pos hx]
    rw [hq, List.idxOf_cons_eq tail rfl]
  · have h_in_q' : x ∈ (fifo_fetch hk q v hv).pages := by
      rw [hq']
      exact List.mem_append_left [v] hx_tail
    have h_x_ne_hd : head ≠ x := by
      rintro rfl
      exact hhd hx_tail
    unfold fifo_rank
    rw [if_pos h_in_q', if_pos hx]
    rw [hq, List.idxOf_cons_ne tail h_x_ne_hd]
    rw [hq', List.idxOf_append_of_mem hx_tail]
    omega

lemma rank_potential_online_payment_bound_diff_old {α : Type*} [DecidableEq α] {k : ℕ} (hk : 1 ≤ k) (q : FifoQueue α k) (v : α) (hv : v ∉ q.pages)
    (x : α) (hx : x ∈ q.pages) :
    (fifo_rank (fifo_fetch hk q v hv) x : ℤ) - (fifo_rank q x : ℤ) = -1 := by
  have h_fetch := rank_potential_online_payment_bound_fetch_old hk q v hv x hx
  have h_pos : 1 ≤ fifo_rank q x := by
    unfold fifo_rank
    rw [if_pos hx]
    omega
  omega

lemma rank_potential_online_payment_bound_rank_not_mem {α : Type*} [DecidableEq α] {k : ℕ} (q : FifoQueue α k) (x : α) (hx : x ∉ q.pages) :
    fifo_rank q x = 0 := by
  unfold fifo_rank
  rw [if_neg hx]

lemma rank_potential_online_payment_bound_eq_sum {α : Type*} [DecidableEq α] {k : ℕ} (q : FifoQueue α k) (cOpt : Finset α) (S : Finset α)
    (hS : q.pages.toFinset ⊆ S) :
    rank_potential q cOpt = ∑ x ∈ S \ cOpt, fifo_rank q x := by
  unfold rank_potential
  have h_sub : q.pages.toFinset \ cOpt ⊆ S \ cOpt := Finset.sdiff_subset_sdiff hS subset_rfl
  rw [← Finset.sum_subset h_sub]
  intro x hx hnot
  rw [Finset.mem_sdiff] at hx hnot
  have h_not_q : x ∉ q.pages.toFinset := by
    intro h
    exact hnot ⟨h, hx.2⟩
  rw [List.mem_toFinset] at h_not_q
  unfold fifo_rank
  rw [if_neg h_not_q]

lemma rank_potential_online_payment_bound_fetch_subset {α : Type*} [DecidableEq α] {k : ℕ} (hk : 1 ≤ k) (q : FifoQueue α k) (v : α) (hv : v ∉ q.pages) :
    (fifo_fetch hk q v hv).pages.toFinset ⊆ insert v q.pages.toFinset := by
  rcases q with ⟨_ | ⟨head, tail⟩, hlen, hnodup⟩
  · simp at hlen; omega
  · intro x hx
    simp only [List.mem_toFinset, Finset.mem_insert] at hx ⊢
    have : (fifo_fetch hk ⟨head :: tail, hlen, hnodup⟩ v hv).pages = tail ++ [v] := rfl
    rw [this] at hx
    simp only [List.mem_append, List.mem_singleton] at hx
    rcases hx with hx_tail | rfl
    · right; exact List.mem_cons_of_mem head hx_tail
    · left; rfl

lemma rank_potential_online_payment_bound_card_sdiff_ge_one {α : Type*} [DecidableEq α] {k : ℕ} (q : FifoQueue α k) (cOpt : Finset α)
    (v : α) (hv : v ∉ q.pages) (hc : cOpt.card = k) (hv_c : v ∈ cOpt) :
    1 ≤ (q.pages.toFinset \ cOpt).card := by
  have hq_card : q.pages.toFinset.card = k := by
    rw [List.toFinset_card_of_nodup q.nodup, q.length_eq]
  by_contra h
  have h0 : (q.pages.toFinset \ cOpt).card = 0 := by omega
  rw [Finset.card_eq_zero, Finset.sdiff_eq_empty_iff_subset] at h0
  have heq : q.pages.toFinset = cOpt := by
    apply Finset.eq_of_subset_of_card_le h0
    omega
  have hv_in : v ∈ q.pages.toFinset := by
    rw [heq]
    exact hv_c
  rw [List.mem_toFinset] at hv_in
  exact hv hv_in

lemma rank_potential_online_payment_bound_insert_sdiff_mem {α : Type*} [DecidableEq α] (s t : Finset α) (x : α) (hx : x ∈ t) :
    insert x s \ t = s \ t := by
  ext y
  simp only [Finset.mem_sdiff, Finset.mem_insert]
  constructor
  · rintro ⟨rfl | hy, hyt⟩
    · exact (hyt hx).elim
    · exact ⟨hy, hyt⟩
  · rintro ⟨hy, hyt⟩
    exact ⟨Or.inr hy, hyt⟩

lemma rank_potential_online_payment_bound_insert_sdiff_not_mem {α : Type*} [DecidableEq α] (s t : Finset α) (x : α) (hx : x ∉ t) :
    insert x s \ t = insert x (s \ t) := by
  ext y
  simp only [Finset.mem_sdiff, Finset.mem_insert]
  constructor
  · rintro ⟨rfl | hy, hyt⟩
    · exact Or.inl rfl
    · exact Or.inr ⟨hy, hyt⟩
  · rintro (rfl | ⟨hy, hyt⟩)
    · exact ⟨Or.inl rfl, hx⟩
    · exact ⟨Or.inr hy, hyt⟩

/-- Potential change at an online payment: at most -1 if v in Opt, at most k always. -/
theorem rank_potential_online_payment_bound {α : Type*} [DecidableEq α] {k : ℕ} (hk : 1 ≤ k) (q : FifoQueue α k) (cOpt : Finset α) (v : α) (hv : v ∉ q.pages) (hc : cOpt.card = k) : ((v ∈ cOpt → (rank_potential (fifo_fetch hk q v hv) cOpt : ℤ) - (rank_potential q cOpt : ℤ) ≤ -1) ∧ ((rank_potential (fifo_fetch hk q v hv) cOpt : ℤ) - (rank_potential q cOpt : ℤ) ≤ (k : ℤ))) := by
  set q' := fifo_fetch hk q v hv
  set S := insert v q.pages.toFinset
  have hS_q : q.pages.toFinset ⊆ S := Finset.subset_insert v q.pages.toFinset
  have hS_q' : q'.pages.toFinset ⊆ S := rank_potential_online_payment_bound_fetch_subset hk q v hv
  have h_sum_q : rank_potential q cOpt = ∑ x ∈ S \ cOpt, fifo_rank q x :=
    rank_potential_online_payment_bound_eq_sum q cOpt S hS_q
  have h_sum_q' : rank_potential q' cOpt = ∑ x ∈ S \ cOpt, fifo_rank q' x :=
    rank_potential_online_payment_bound_eq_sum q' cOpt S hS_q'
  have h_diff : (rank_potential q' cOpt : ℤ) - (rank_potential q cOpt : ℤ) =
      ∑ x ∈ S \ cOpt, ((fifo_rank q' x : ℤ) - (fifo_rank q x : ℤ)) := by
    rw [h_sum_q, h_sum_q']
    push_cast
    rw [← Finset.sum_sub_distrib]
  have h_q_term : ∀ x ∈ q.pages.toFinset \ cOpt, (fifo_rank q' x : ℤ) - (fifo_rank q x : ℤ) = -1 := by
    intro x hx
    rw [Finset.mem_sdiff, List.mem_toFinset] at hx
    exact rank_potential_online_payment_bound_diff_old hk q v hv x hx.1
  have h_sum_q_terms : ∑ x ∈ q.pages.toFinset \ cOpt, ((fifo_rank q' x : ℤ) - (fifo_rank q x : ℤ)) =
      - ((q.pages.toFinset \ cOpt).card : ℤ) := by
    have : ∑ x ∈ q.pages.toFinset \ cOpt, ((fifo_rank q' x : ℤ) - (fifo_rank q x : ℤ)) =
        ∑ x ∈ q.pages.toFinset \ cOpt, (-1 : ℤ) := Finset.sum_congr rfl h_q_term
    rw [this, Finset.sum_const, nsmul_eq_mul]
    ring
  by_cases hvc : v ∈ cOpt
  · have hS_sdiff : S \ cOpt = q.pages.toFinset \ cOpt :=
      rank_potential_online_payment_bound_insert_sdiff_mem q.pages.toFinset cOpt v hvc
    rw [hS_sdiff, h_sum_q_terms] at h_diff
    have h_card_ge : 1 ≤ (q.pages.toFinset \ cOpt).card :=
      rank_potential_online_payment_bound_card_sdiff_ge_one q cOpt v hv hc hvc
    constructor
    · intro _
      omega
    · omega
  · have hS_sdiff : S \ cOpt = insert v (q.pages.toFinset \ cOpt) :=
      rank_potential_online_payment_bound_insert_sdiff_not_mem q.pages.toFinset cOpt v hvc
    have hv_not_sdiff : v ∉ q.pages.toFinset \ cOpt := by
      intro h
      rw [Finset.mem_sdiff, List.mem_toFinset] at h
      exact hv h.1
    rw [hS_sdiff, Finset.sum_insert hv_not_sdiff, h_sum_q_terms] at h_diff
    have hv_q' : fifo_rank q' v = k := rank_potential_online_payment_bound_fetch_v hk q v hv
    have hv_q : fifo_rank q v = 0 := rank_potential_online_payment_bound_rank_not_mem q v hv
    rw [hv_q', hv_q] at h_diff
    constructor
    · intro h
      exact (hvc h).elim
    · omega
