import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphNonneighborKernelOrDominatingVertex
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# digraph_nonneighborhood_kernels_weighted_half_cover

Topic: graphs   Node: e80ba37b96f7

Provenance: original. Related work: A proposed consequence of the deletion argument in the proof of Theorem 3.4(1) in https://www.combinatorics.org/ojs/index.php/eljc/article/download/v33i1p32/pdf/; related weighted transfer is https://arxiv.org/abs/2610.23487. No novelty is claimed until literature is checked more fully.

In a finite loopless oriented graph in which the induced non-neighborhood of every vertex has an out-kernel, every nonnegative integer weighting has a quasi-kernel whose closed out-neighborhood contains at least half the total weight.
-/

def digraph_nonneighborhood_kernels_weighted_half_cover_Nin
    {α : Type} [Fintype α] [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj] (v : α) : Finset α :=
  Finset.univ.filter (fun z => D.Adj z v)

def digraph_nonneighborhood_kernels_weighted_half_cover_win
    {α : Type} [Fintype α] [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj] (w : α → ℕ) (v : α) : ℕ :=
  ∑ z ∈ digraph_nonneighborhood_kernels_weighted_half_cover_Nin D v, w z

lemma digraph_nonneighborhood_kernels_weighted_half_cover_win_eq_sum_ite
    {α : Type} [Fintype α] [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj] (w : α → ℕ) (v : α) :
    digraph_nonneighborhood_kernels_weighted_half_cover_win D w v = ∑ u, if D.Adj u v then w u else 0 := by
  dsimp [digraph_nonneighborhood_kernels_weighted_half_cover_win, digraph_nonneighborhood_kernels_weighted_half_cover_Nin]
  rw [Finset.sum_filter]

lemma digraph_nonneighborhood_kernels_weighted_half_cover_mul_win_eq
    {α : Type} [Fintype α] [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj] (w : α → ℕ) (v : α) :
    w v * digraph_nonneighborhood_kernels_weighted_half_cover_win D w v = ∑ u, if D.Adj u v then w v * w u else 0 := by
  rw [digraph_nonneighborhood_kernels_weighted_half_cover_win_eq_sum_ite, Finset.mul_sum]
  congr 1; ext u
  split_ifs <;> ring

lemma digraph_nonneighborhood_kernels_weighted_half_cover_test_pt
    {α : Type} (D : Digraph α) [DecidableRel D.Adj]
    (horient : ∀ u v, D.Adj u v → ¬ D.Adj v u) (w : α → ℕ) (u v : α) :
    ((if D.Adj v u then w u * w v else 0) + (if D.Adj u v then w v * w u else 0)) ≤ w u * w v := by
  by_cases hvu : D.Adj v u
  · have huv : ¬ D.Adj u v := horient v u hvu
    rw [if_pos hvu, if_neg huv]
    omega
  · by_cases huv : D.Adj u v
    · rw [if_neg hvu, if_pos huv, mul_comm (w v)]
      omega
    · rw [if_neg hvu, if_neg huv]
      omega

lemma digraph_nonneighborhood_kernels_weighted_half_cover_double_sum_oriented
    {α : Type} [Fintype α] [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj]
    (horient : ∀ u v, D.Adj u v → ¬ D.Adj v u) (w : α → ℕ) :
    2 * (∑ v, w v * digraph_nonneighborhood_kernels_weighted_half_cover_win D w v) ≤ (∑ v, w v) * (∑ v, w v) := by
  simp_rw [digraph_nonneighborhood_kernels_weighted_half_cover_mul_win_eq]
  rw [two_mul]
  nth_rewrite 2 [Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  have h_cong : (fun u => (∑ v, if D.Adj v u then w u * w v else 0) +
      (∑ v, if D.Adj u v then w v * w u else 0)) =
      fun u => ∑ v, ((if D.Adj v u then w u * w v else 0) + (if D.Adj u v then w v * w u else 0)) := by
    ext u; exact (Finset.sum_add_distrib).symm
  rw [h_cong]
  have h_outer : (∑ v, w v) * (∑ v, w v) = ∑ u, ∑ v, w u * w v := by
    rw [Finset.sum_mul]; congr 1; ext u; rw [Finset.mul_sum]
  rw [h_outer]
  exact Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ =>
    digraph_nonneighborhood_kernels_weighted_half_cover_test_pt D horient w u v

lemma digraph_nonneighborhood_kernels_weighted_half_cover_win_min_bound
    {α : Type} [Fintype α] [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj]
    (w : α → ℕ) (s : α)
    (hmin : ∀ v, digraph_nonneighborhood_kernels_weighted_half_cover_win D w s ≤
      digraph_nonneighborhood_kernels_weighted_half_cover_win D w v)
    (hbound : 2 * (∑ v, w v * digraph_nonneighborhood_kernels_weighted_half_cover_win D w v) ≤
      (∑ v, w v) * (∑ v, w v))
    (hpos : 0 < ∑ v, w v) :
    2 * digraph_nonneighborhood_kernels_weighted_half_cover_win D w s ≤ ∑ v, w v := by
  have hsum : (∑ v, w v) * (2 * digraph_nonneighborhood_kernels_weighted_half_cover_win D w s) ≤
      2 * (∑ v, w v * digraph_nonneighborhood_kernels_weighted_half_cover_win D w v) := by
    rw [mul_comm (∑ v, w v), mul_assoc]
    apply Nat.mul_le_mul_left 2
    rw [mul_comm, Finset.sum_mul]
    apply Finset.sum_le_sum
    intro v _
    exact Nat.mul_le_mul_left (w v) (hmin v)
  have hcomb : (∑ v, w v) * (2 * digraph_nonneighborhood_kernels_weighted_half_cover_win D w s) ≤
      (∑ v, w v) * (∑ v, w v) := by omega
  exact Nat.le_of_mul_le_mul_left hcomb hpos

def digraph_nonneighborhood_kernels_weighted_half_cover_M (α : Type) [Fintype α] : ℕ :=
  Fintype.card α + 1

theorem digraph_nonneighborhood_kernels_weighted_half_cover_enc_lt
    (M : ℕ) (w1 w2 c1 c2 : ℕ) (hc1 : c1 < M)
    (h : w1 < w2 ∨ (w1 ≤ w2 ∧ c1 < c2)) :
    w1 * M + c1 < w2 * M + c2 := by
  rcases h with hlt | ⟨hle, hlt⟩
  · nlinarith
  · rcases eq_or_lt_of_le hle with rfl | hlt2
    · nlinarith
    · nlinarith

theorem digraph_nonneighborhood_kernels_weighted_half_cover_enc_min
    (α : Type) [Fintype α] {f_w f_c : α → ℕ} {s u : α}
    (hc : ∀ x, f_c x < digraph_nonneighborhood_kernels_weighted_half_cover_M α)
    (hmin : ∀ x, f_w s * digraph_nonneighborhood_kernels_weighted_half_cover_M α + f_c s ≤
      f_w x * digraph_nonneighborhood_kernels_weighted_half_cover_M α + f_c x) :
    f_w s ≤ f_w u := by
  by_contra! h
  have hlt := digraph_nonneighborhood_kernels_weighted_half_cover_enc_lt
    (digraph_nonneighborhood_kernels_weighted_half_cover_M α)
    (f_w u) (f_w s) (f_c u) (f_c s) (hc u) (Or.inl h)
  have hle := hmin u
  omega

lemma digraph_nonneighborhood_kernels_weighted_half_cover_win_le_and_card_lt
    {α : Type} [Fintype α] [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj]
    (hloop : ∀ v, ¬ D.Adj v v) (w : α → ℕ) (s t : α)
    (hts : D.Adj t s) (htsub : ∀ z, D.Adj z t → D.Adj z s) :
    digraph_nonneighborhood_kernels_weighted_half_cover_win D w t <
      digraph_nonneighborhood_kernels_weighted_half_cover_win D w s ∨
    (digraph_nonneighborhood_kernels_weighted_half_cover_win D w t ≤
      digraph_nonneighborhood_kernels_weighted_half_cover_win D w s ∧
      (digraph_nonneighborhood_kernels_weighted_half_cover_Nin D t).card <
        (digraph_nonneighborhood_kernels_weighted_half_cover_Nin D s).card) := by
  have ht_in_s : t ∈ digraph_nonneighborhood_kernels_weighted_half_cover_Nin D s := by
    simp [digraph_nonneighborhood_kernels_weighted_half_cover_Nin, hts]
  have hsub : digraph_nonneighborhood_kernels_weighted_half_cover_Nin D t ⊆
      (digraph_nonneighborhood_kernels_weighted_half_cover_Nin D s).erase t := by
    intro z hz
    simp only [Finset.mem_erase, digraph_nonneighborhood_kernels_weighted_half_cover_Nin,
      Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
    refine ⟨?_, htsub z hz⟩
    intro heq
    subst heq
    exact hloop z hz
  have hcard : (digraph_nonneighborhood_kernels_weighted_half_cover_Nin D t).card ≤
      ((digraph_nonneighborhood_kernels_weighted_half_cover_Nin D s).erase t).card :=
    Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem ht_in_s] at hcard
  have hcard_lt : (digraph_nonneighborhood_kernels_weighted_half_cover_Nin D t).card <
      (digraph_nonneighborhood_kernels_weighted_half_cover_Nin D s).card := by
    have : 1 ≤ (digraph_nonneighborhood_kernels_weighted_half_cover_Nin D s).card :=
      Finset.card_pos.mpr ⟨t, ht_in_s⟩
    omega
  have hwin_le : digraph_nonneighborhood_kernels_weighted_half_cover_win D w t ≤
      ∑ z ∈ (digraph_nonneighborhood_kernels_weighted_half_cover_Nin D s).erase t, w z := by
    dsimp [digraph_nonneighborhood_kernels_weighted_half_cover_win]
    exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)
  have hwin_split : digraph_nonneighborhood_kernels_weighted_half_cover_win D w s =
      (∑ z ∈ (digraph_nonneighborhood_kernels_weighted_half_cover_Nin D s).erase t, w z) + w t := by
    dsimp [digraph_nonneighborhood_kernels_weighted_half_cover_win]
    exact (Finset.sum_erase_add (digraph_nonneighborhood_kernels_weighted_half_cover_Nin D s) w ht_in_s).symm
  by_cases hwt : w t = 0
  · right
    refine ⟨by omega, hcard_lt⟩
  · left
    omega

lemma digraph_nonneighborhood_kernels_weighted_half_cover_cover_weight_ge
    {α : Type} [Fintype α] [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj]
    (w : α → ℕ) (s : α) (Q : Finset α)
    (hcov : ∀ x, ¬ D.Adj x s → ∃ q ∈ Q, q = x ∨ D.Adj q x) :
    ∑ v, w v ≤ (∑ v ∈ Finset.univ.filter (fun v => ∃ q ∈ Q, q = v ∨ D.Adj q v), w v) +
      digraph_nonneighborhood_kernels_weighted_half_cover_win D w s := by
  let C := Finset.univ.filter (fun v => ∃ q ∈ Q, q = v ∨ D.Adj q v)
  have h_split : ∑ v, w v = (∑ v ∈ C, w v) + (∑ v ∈ Finset.univ \ C, w v) := by
    rw [← Finset.sum_sdiff (Finset.subset_univ C), add_comm]
  rw [h_split]
  apply Nat.add_le_add_left
  have hsub : Finset.univ \ C ⊆ digraph_nonneighborhood_kernels_weighted_half_cover_Nin D s := by
    intro x hx
    simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, Finset.mem_filter, not_exists, C] at hx
    simp only [digraph_nonneighborhood_kernels_weighted_half_cover_Nin, Finset.mem_filter, Finset.mem_univ, true_and]
    by_contra hnot
    have : ∃ q ∈ Q, q = x ∨ D.Adj q x := hcov x hnot
    rcases this with ⟨q, hq, hq2⟩
    exact hx q ⟨hq, hq2⟩
  dsimp [digraph_nonneighborhood_kernels_weighted_half_cover_win]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => Nat.zero_le _)

theorem digraph_nonneighborhood_kernels_weighted_half_cover
    {α : Type} [Fintype α] [DecidableEq α]
    (D : Digraph α) [DecidableRel D.Adj]
    (hloop : ∀ v, ¬ D.Adj v v)
    (horient : ∀ u v, D.Adj u v → ¬ D.Adj v u)
    (hlocal : ∀ v, ∃ K : Finset α,
      (∀ x ∈ K, x ≠ v ∧ ¬ D.Adj x v ∧ ¬ D.Adj v x) ∧
      (∀ x ∈ K, ∀ y ∈ K, x ≠ y → ¬ D.Adj x y) ∧
      (∀ x, x ≠ v → ¬ D.Adj x v → ¬ D.Adj v x →
        ∃ k ∈ K, k = x ∨ D.Adj k x)) (w : α → ℕ) :
    ∃ Q : Finset α,
      (∀ u ∈ Q, ∀ v ∈ Q, u ≠ v → ¬ D.Adj u v) ∧
      (∀ v, ∃ u ∈ Q, u = v ∨ D.Adj u v ∨ ∃ z, D.Adj u z ∧ D.Adj z v) ∧
      (∑ v ∈ Finset.univ, w v) ≤
        2 * (∑ v ∈ Finset.univ.filter (fun v => ∃ q ∈ Q, q = v ∨ D.Adj q v), w v) := by
  by_cases hemp : IsEmpty α
  · refine ⟨∅, by simp, fun v => isEmptyElim v, by simp⟩
  · have hnon : Nonempty α := not_isEmpty_iff.mp hemp
    have huniv : (Finset.univ : Finset α).Nonempty := Finset.univ_nonempty
    let score : α → ℕ := fun v =>
      digraph_nonneighborhood_kernels_weighted_half_cover_win D w v *
        digraph_nonneighborhood_kernels_weighted_half_cover_M α +
        (digraph_nonneighborhood_kernels_weighted_half_cover_Nin D v).card
    obtain ⟨s, hs_univ, hs_min⟩ := Finset.exists_min_image Finset.univ score huniv
    have hNin_lt : ∀ x : α, (digraph_nonneighborhood_kernels_weighted_half_cover_Nin D x).card <
        digraph_nonneighborhood_kernels_weighted_half_cover_M α := fun x => by
      dsimp [digraph_nonneighborhood_kernels_weighted_half_cover_M]
      have := Finset.card_le_univ (digraph_nonneighborhood_kernels_weighted_half_cover_Nin D x)
      omega
    have hwin_min : ∀ v, digraph_nonneighborhood_kernels_weighted_half_cover_win D w s ≤
        digraph_nonneighborhood_kernels_weighted_half_cover_win D w v := fun v =>
      digraph_nonneighborhood_kernels_weighted_half_cover_enc_min α hNin_lt (fun x => hs_min x (Finset.mem_univ x))
    obtain ⟨K, hK, hind, hdom⟩ := hlocal s
    rcases digraph_nonneighbor_kernel_or_dominating_vertex D s K hK hind hdom with
      ⟨hQind, hQcov⟩ | ⟨t, htsne, hts, htsub⟩
    · refine ⟨insert s K, hQind, hQcov, ?_⟩
      have hcov : ∀ x, ¬ D.Adj x s → ∃ q ∈ insert s K, q = x ∨ D.Adj q x := by
        intro x hxs
        by_cases hx_eq : x = s
        · subst x; exact ⟨s, Finset.mem_insert_self s K, Or.inl rfl⟩
        · by_cases hsx : D.Adj s x
          · exact ⟨s, Finset.mem_insert_self s K, Or.inr hsx⟩
          · obtain ⟨k, hk, hkx⟩ := hdom x hx_eq hxs hsx
            exact ⟨k, Finset.mem_insert_of_mem hk, hkx⟩
      have hcov_w := digraph_nonneighborhood_kernels_weighted_half_cover_cover_weight_ge D w s (insert s K) hcov
      by_cases hW : (∑ v, w v) = 0
      · omega
      · have hWpos : 0 < ∑ v, w v := Nat.pos_of_ne_zero hW
        have hds := digraph_nonneighborhood_kernels_weighted_half_cover_double_sum_oriented D horient w
        have hbound := digraph_nonneighborhood_kernels_weighted_half_cover_win_min_bound D w s hwin_min hds hWpos
        omega
    · exfalso
      have hlt := digraph_nonneighborhood_kernels_weighted_half_cover_win_le_and_card_lt D hloop w s t hts htsub
      have hlt_score : score t < score s := by
        dsimp [score]
        exact digraph_nonneighborhood_kernels_weighted_half_cover_enc_lt
          (digraph_nonneighborhood_kernels_weighted_half_cover_M α)
          (digraph_nonneighborhood_kernels_weighted_half_cover_win D w t)
          (digraph_nonneighborhood_kernels_weighted_half_cover_win D w s)
          (digraph_nonneighborhood_kernels_weighted_half_cover_Nin D t).card
          (digraph_nonneighborhood_kernels_weighted_half_cover_Nin D s).card (hNin_lt t) hlt
      have hle := hs_min t (Finset.mem_univ t)
      omega
