import AFTD.Prelude
import AFTD.Kb.Tcs.BpeWorstRatio
import AFTD.Kb.Tcs.BpeGreedyStep
import AFTD.Kb.Tcs.BpeSteps
import AFTD.Kb.Tcs.BpePairCount
import AFTD.Kb.Tcs.BpeOptimalUtility
import AFTD.Kb.Tcs.BpeMaxPairCount
import AFTD.Kb.Tcs.BpeFullMerge
import AFTD.Kb.Tcs.BpePartialMerge
import AFTD.Kb.Tcs.BpePartialStep

/-!
# bpe_worst_case_ratio_three_upper_bound

Topic: algorithms   Node: c54447900f96

Provenance: formalization of a published result. Source: arXiv:2611.08671, Proposition 13.

The worst-case ratio of greedy Byte-Pair Encoding to optimal partial-merge utility for three merges is at most 7/12.
-/

theorem bpe3ub_pc_cons_ne (a b c : ℕ) (h : c ≠ a) (r : List ℕ) :
    bpe_pair_count a b (c :: r) = bpe_pair_count a b r := by
  cases r with
  | nil => simp [bpe_pair_count]
  | cons y ys => simp [bpe_pair_count, h]

theorem bpe3ub_pc_append (a b c : ℕ) (hca : c ≠ a) (hcb : c ≠ b) :
    ∀ (w r : List ℕ), bpe_pair_count a b (w ++ c :: r) =
      bpe_pair_count a b w + bpe_pair_count a b r
  | [], r => by simpa [bpe_pair_count] using bpe3ub_pc_cons_ne a b c hca r
  | [x], r => by
      simp only [List.cons_append, List.nil_append, bpe_pair_count, hcb, and_false,
        if_false, zero_add]
      exact bpe3ub_pc_cons_ne a b c hca r
  | x :: y :: xs, r => by
      have h1 := bpe3ub_pc_append a b c hca hcb xs r
      have h2 := bpe3ub_pc_append a b c hca hcb (y :: xs) r
      simp only [List.cons_append] at h2 ⊢
      simp only [bpe_pair_count]
      split_ifs <;> simp only [h1, h2]; omega

theorem bpe3ub_fm_cons_ne (a b c z : ℕ) (h : c ≠ a) (r : List ℕ) :
    bpe_full_merge a b z (c :: r) = c :: bpe_full_merge a b z r := by
  cases r with
  | nil => simp [bpe_full_merge]
  | cons y ys => simp [bpe_full_merge, h]

theorem bpe3ub_fm_append (a b c z : ℕ) (hca : c ≠ a) (hcb : c ≠ b) :
    ∀ (w r : List ℕ), bpe_full_merge a b z (w ++ c :: r) =
      bpe_full_merge a b z w ++ c :: bpe_full_merge a b z r
  | [], r => by simpa [bpe_full_merge] using bpe3ub_fm_cons_ne a b c z hca r
  | [x], r => by
      simp only [List.cons_append, List.nil_append, bpe_full_merge, hcb, and_false,
        if_false]
      rw [bpe3ub_fm_cons_ne a b c z hca r]
  | x :: y :: xs, r => by
      have h1 := bpe3ub_fm_append a b c z hca hcb xs r
      have h2 := bpe3ub_fm_append a b c z hca hcb (y :: xs) r
      simp only [List.cons_append] at h2 ⊢
      simp only [bpe_full_merge]
      split_ifs <;> simp [h1, h2]

theorem bpe3ub_pc_le_count_left (a b : ℕ) :
    ∀ s : List ℕ, bpe_pair_count a b s ≤ s.count a
  | [] => by simp [bpe_pair_count]
  | [x] => by simp [bpe_pair_count]
  | x :: y :: xs => by
      have h1 := bpe3ub_pc_le_count_left a b xs
      have h2 := bpe3ub_pc_le_count_left a b (y :: xs)
      simp only [bpe_pair_count]
      split_ifs with h
      · obtain ⟨rfl, rfl⟩ := h
        simp only [List.count_cons_self]
        have : xs.count x ≤ (y :: xs).count x := by simp [List.count_cons]
        omega
      · rw [List.count_cons]; omega

theorem bpe3ub_pc_le_count_right (a b : ℕ) :
    ∀ s : List ℕ, bpe_pair_count a b s ≤ s.count b
  | [] => by simp [bpe_pair_count]
  | [x] => by simp [bpe_pair_count]
  | x :: y :: xs => by
      have h1 := bpe3ub_pc_le_count_right a b xs
      have h2 := bpe3ub_pc_le_count_right a b (y :: xs)
      simp only [bpe_pair_count]
      split_ifs with h
      · obtain ⟨rfl, rfl⟩ := h
        simp only [List.count_cons, beq_self_eq_true, if_true]
        split_ifs <;> omega
      · rw [List.count_cons]; omega

theorem bpe3ub_pc_pos_mem (a b : ℕ) :
    ∀ s : List ℕ, 0 < bpe_pair_count a b s → (a, b) ∈ s.zip s.tail
  | [] => by simp [bpe_pair_count]
  | [x] => by simp [bpe_pair_count]
  | x :: y :: xs => by
      intro hpos
      simp only [bpe_pair_count] at hpos
      split_ifs at hpos with h
      · obtain ⟨rfl, rfl⟩ := h
        simp
      · have := bpe3ub_pc_pos_mem a b (y :: xs) hpos
        simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons] at this ⊢
        exact Or.inr this

theorem bpe3ub_pc_le_max (a b : ℕ) (s : List ℕ) :
    bpe_pair_count a b s ≤ bpe_max_pair_count s := by
  rcases Nat.eq_zero_or_pos (bpe_pair_count a b s) with h | h
  · omega
  · unfold bpe_max_pair_count
    exact Finset.le_sup (f := fun p : ℕ × ℕ => bpe_pair_count p.1 p.2 s)
      (List.mem_toFinset.mpr (bpe3ub_pc_pos_mem a b s h))

theorem bpe3ub_partial_of_full (a b z : ℕ) :
    ∀ s : List ℕ, bpe_partial_merge a b z s (bpe_full_merge a b z s)
  | [] => by simp [bpe_partial_merge, bpe_full_merge]
  | [x] => by simp [bpe_partial_merge, bpe_full_merge]
  | x :: y :: xs => by
      have h1 := bpe3ub_partial_of_full a b z xs
      have h2 := bpe3ub_partial_of_full a b z (y :: xs)
      simp only [bpe_full_merge]
      split_ifs with h
      · obtain ⟨rfl, rfl⟩ := h
        exact Or.inr ⟨rfl, rfl, _, rfl, h1⟩
      · exact Or.inl ⟨_, rfl, h2⟩

def bpe3ub_sepJoin : ℕ → List (List ℕ) → List ℕ
  | _, [] => []
  | k, w :: ws => w ++ k :: bpe3ub_sepJoin (k + 1) ws

theorem bpe3ub_pc_sepJoin (a b : ℕ) :
    ∀ (L : List (List ℕ)) (k : ℕ), a < k → b < k →
      bpe_pair_count a b (bpe3ub_sepJoin k L) = (L.map (bpe_pair_count a b)).sum
  | [], k, _, _ => by simp [bpe3ub_sepJoin, bpe_pair_count]
  | w :: ws, k, ha, hb => by
      simp only [bpe3ub_sepJoin, List.map_cons, List.sum_cons]
      rw [bpe3ub_pc_append a b k (by omega) (by omega),
        bpe3ub_pc_sepJoin a b ws (k + 1) (by omega) (by omega)]

theorem bpe3ub_fm_sepJoin (a b z : ℕ) :
    ∀ (L : List (List ℕ)) (k : ℕ), a < k → b < k →
      bpe_full_merge a b z (bpe3ub_sepJoin k L) =
        bpe3ub_sepJoin k (L.map (bpe_full_merge a b z))
  | [], k, _, _ => by simp [bpe3ub_sepJoin, bpe_full_merge]
  | w :: ws, k, ha, hb => by
      simp only [bpe3ub_sepJoin, List.map_cons]
      rw [bpe3ub_fm_append a b k z (by omega) (by omega),
        bpe3ub_fm_sepJoin a b z ws (k + 1) (by omega) (by omega)]

theorem bpe3ub_length_sepJoin :
    ∀ (L : List (List ℕ)) (k : ℕ),
      (bpe3ub_sepJoin k L).length = (L.map List.length).sum + L.length
  | [], k => by simp [bpe3ub_sepJoin]
  | w :: ws, k => by
      simp only [bpe3ub_sepJoin, List.length_append, List.length_cons, List.map_cons,
        List.sum_cons, bpe3ub_length_sepJoin ws (k + 1)]
      omega

theorem bpe3ub_mem_sepJoin (m : ℕ) :
    ∀ (L : List (List ℕ)) (k : ℕ), m ∈ bpe3ub_sepJoin k L → (∃ w ∈ L, m ∈ w) ∨ k ≤ m
  | [], k => by simp [bpe3ub_sepJoin]
  | w :: ws, k => by
      intro hm
      simp only [bpe3ub_sepJoin, List.mem_append, List.mem_cons] at hm
      rcases hm with hm | rfl | hm
      · exact Or.inl ⟨w, by simp, hm⟩
      · exact Or.inr le_rfl
      · rcases bpe3ub_mem_sepJoin m ws (k + 1) hm with ⟨v, hv, hmv⟩ | h
        · exact Or.inl ⟨v, by simp [hv], hmv⟩
        · exact Or.inr (by omega)

theorem bpe3ub_count_sepJoin (m : ℕ) :
    ∀ (L : List (List ℕ)) (k : ℕ), (∀ w ∈ L, ∀ x ∈ w, x < k) → k ≤ m →
      (bpe3ub_sepJoin k L).count m ≤ 1
  | [], k, _, _ => by simp [bpe3ub_sepJoin]
  | w :: ws, k, hL, hk => by
      simp only [bpe3ub_sepJoin, List.count_append, List.count_cons]
      have hw : w.count m = 0 := by
        rw [List.count_eq_zero]
        intro hm
        have := hL w (by simp) m hm
        omega
      rcases Nat.eq_or_lt_of_le hk with rfl | hlt
      · have : (bpe3ub_sepJoin (k + 1) ws).count k = 0 := by
          rw [List.count_eq_zero]
          intro hm
          rcases bpe3ub_mem_sepJoin k ws (k + 1) hm with ⟨v, hv, hmv⟩ | h
          · have := hL v (by simp [hv]) k hmv
            omega
          · omega
        simp [hw, this]
      · have := bpe3ub_count_sepJoin m ws (k + 1)
          (fun v hv x hx => Nat.lt_succ_of_lt (hL v (by simp [hv]) x hx)) hlt
        have hne : (k == m) = false := by simp; omega
        simp [hw, hne]
        omega

theorem bpe3ub_max_le (L : List (List ℕ)) (k M : ℕ) (hM : 1 ≤ M)
    (hL : ∀ w ∈ L, ∀ x ∈ w, x < k)
    (h : ∀ a < k, ∀ b < k, (L.map (bpe_pair_count a b)).sum ≤ M) :
    bpe_max_pair_count (bpe3ub_sepJoin k L) ≤ M := by
  unfold bpe_max_pair_count
  apply Finset.sup_le
  rintro ⟨a, b⟩ _
  dsimp only
  by_cases ha : a < k
  · by_cases hb : b < k
    · rw [bpe3ub_pc_sepJoin a b L k ha hb]
      exact h a ha b hb
    · have := bpe3ub_pc_le_count_right a b (bpe3ub_sepJoin k L)
      have := bpe3ub_count_sepJoin b L k hL (by omega)
      omega
  · have := bpe3ub_pc_le_count_left a b (bpe3ub_sepJoin k L)
    have := bpe3ub_count_sepJoin a L k hL (by omega)
    omega

def bpe3ub_blocks (n : ℕ) (Ws E : List (List ℕ)) : List (List ℕ) :=
  Ws.flatMap (List.replicate n) ++ E

theorem bpe3ub_map_blocks (f : List ℕ → List ℕ) (n : ℕ) (Ws E : List (List ℕ)) :
    (bpe3ub_blocks n Ws E).map f = bpe3ub_blocks n (Ws.map f) (E.map f) := by
  induction Ws with
  | nil => simp [bpe3ub_blocks]
  | cons w ws ih =>
      simp only [bpe3ub_blocks, List.flatMap_cons, List.map_append, List.map_cons,
        List.map_replicate] at ih ⊢
      rw [List.append_assoc, ih, List.append_assoc]

theorem bpe3ub_sum_blocks (g : List ℕ → ℕ) (n : ℕ) (Ws E : List (List ℕ)) :
    ((bpe3ub_blocks n Ws E).map g).sum = n * (Ws.map g).sum + (E.map g).sum := by
  induction Ws with
  | nil => simp [bpe3ub_blocks]
  | cons w ws ih =>
      simp only [bpe3ub_blocks, List.flatMap_cons, List.map_append, List.sum_append,
        List.map_replicate, List.sum_replicate, List.map_cons, List.sum_cons,
        smul_eq_mul] at ih ⊢
      rw [Nat.mul_add]; omega

theorem bpe3ub_length_blocks (n : ℕ) (Ws E : List (List ℕ)) :
    (bpe3ub_blocks n Ws E).length = n * Ws.length + E.length := by
  induction Ws with
  | nil => simp [bpe3ub_blocks]
  | cons w ws ih =>
      simp only [bpe3ub_blocks, List.flatMap_cons, List.length_append,
        List.length_replicate, List.length_cons] at ih ⊢
      rw [Nat.mul_add]; omega

theorem bpe3ub_mem_blocks (n : ℕ) (Ws E : List (List ℕ)) (w : List ℕ)
    (hw : w ∈ bpe3ub_blocks n Ws E) : w ∈ Ws ∨ w ∈ E := by
  simp only [bpe3ub_blocks, List.mem_append, List.mem_flatMap, List.mem_replicate] at hw
  rcases hw with ⟨v, hv, _, rfl⟩ | hw
  · exact Or.inl hv
  · exact Or.inr hw

theorem bpe3ub_notin (n z k : ℕ) (Ws E : List (List ℕ)) (hz : z < k)
    (h1 : ∀ w ∈ Ws, z ∉ w) (h2 : ∀ w ∈ E, z ∉ w) :
    z ∉ bpe3ub_sepJoin k (bpe3ub_blocks n Ws E) := by
  intro hm
  rcases bpe3ub_mem_sepJoin z _ k hm with ⟨w, hw, hzw⟩ | h
  · rcases bpe3ub_mem_blocks n Ws E w hw with h | h
    · exact h1 w h hzw
    · exact h2 w h hzw
  · omega

theorem bpe3ub_lt (n k : ℕ) (Ws E : List (List ℕ))
    (h1 : ∀ w ∈ Ws, ∀ x ∈ w, x < k) (h2 : ∀ w ∈ E, ∀ x ∈ w, x < k) :
    ∀ w ∈ bpe3ub_blocks n Ws E, ∀ x ∈ w, x < k := by
  intro w hw
  rcases bpe3ub_mem_blocks n Ws E w hw with h | h
  · exact h1 w h
  · exact h2 w h

/-- one greedy step on a separator-joined block string -/
theorem bpe3ub_greedy (n M a b z : ℕ) (Ws E : List (List ℕ)) (hM : 1 ≤ M)
    (ha : a < 10) (hb : b < 10) (hz : z < 10)
    (hlt1 : ∀ w ∈ Ws, ∀ x ∈ w, x < 10) (hlt2 : ∀ w ∈ E, ∀ x ∈ w, x < 10)
    (hz1 : ∀ w ∈ Ws, z ∉ w) (hz2 : ∀ w ∈ E, z ∉ w)
    (hall : ∀ a < 10, ∀ b < 10,
      n * (Ws.map (bpe_pair_count a b)).sum + (E.map (bpe_pair_count a b)).sum ≤ M)
    (hab : n * (Ws.map (bpe_pair_count a b)).sum + (E.map (bpe_pair_count a b)).sum = M) :
    bpe_greedy_step (bpe3ub_sepJoin 10 (bpe3ub_blocks n Ws E))
      (bpe3ub_sepJoin 10 (bpe3ub_blocks n (Ws.map (bpe_full_merge a b z))
        (E.map (bpe_full_merge a b z)))) := by
  have hpc : bpe_pair_count a b (bpe3ub_sepJoin 10 (bpe3ub_blocks n Ws E)) = M := by
    rw [bpe3ub_pc_sepJoin a b _ 10 ha hb, bpe3ub_sum_blocks, hab]
  have hmax : bpe_max_pair_count (bpe3ub_sepJoin 10 (bpe3ub_blocks n Ws E)) = M := by
    apply le_antisymm
    · apply bpe3ub_max_le _ 10 M hM (bpe3ub_lt n 10 Ws E hlt1 hlt2)
      intro a ha b hb
      rw [bpe3ub_sum_blocks]
      exact hall a ha b hb
    · rw [← hpc]; exact bpe3ub_pc_le_max a b _
  refine Or.inr ⟨a, b, z, by omega, by rw [hpc, hmax], bpe3ub_notin n z 10 Ws E hz hz1 hz2, ?_⟩
  rw [bpe3ub_fm_sepJoin a b z _ 10 ha hb, bpe3ub_map_blocks]

theorem bpe3ub_partial (n a b z : ℕ) (Ws E : List (List ℕ))
    (ha : a < 10) (hb : b < 10) (hz : z < 10)
    (hz1 : ∀ w ∈ Ws, z ∉ w) (hz2 : ∀ w ∈ E, z ∉ w) :
    bpe_partial_step (bpe3ub_sepJoin 10 (bpe3ub_blocks n Ws E))
      (bpe3ub_sepJoin 10 (bpe3ub_blocks n (Ws.map (bpe_full_merge a b z))
        (E.map (bpe_full_merge a b z)))) := by
  refine Or.inr ⟨a, b, z, bpe3ub_notin n z 10 Ws E hz hz1 hz2, ?_⟩
  rw [← bpe3ub_map_blocks, ← bpe3ub_fm_sepJoin a b z _ 10 ha hb]
  exact bpe3ub_partial_of_full a b z _

theorem bpe3ub_len (n : ℕ) (Ws E : List (List ℕ)) :
    (bpe3ub_sepJoin 10 (bpe3ub_blocks n Ws E)).length =
      n * ((Ws.map List.length).sum + Ws.length) + ((E.map List.length).sum + E.length) := by
  rw [bpe3ub_length_sepJoin, bpe3ub_sum_blocks, bpe3ub_length_blocks]
  ring

/-- blocks of the family: a = 0, b = 1, x = 2 -/
def bpe3ub_W : List (List ℕ) :=
  [[1,2,2,0,1,2,2,0], [2,0,1,0], [1,0,1,0,1,2], [1,2], [2,0], [1,0]]

def bpe3ub_E : List (List ℕ) := [[0,1], [2,2]]

theorem bpe3ub_instance (n : ℕ) (hn : 1 ≤ n) :
    ∃ s t : List ℕ, bpe_steps bpe_greedy_step 3 s t ∧
      12 * n ≤ bpe_optimal_utility s 3 ∧ s.length - t.length = 7 * n + 2 := by
  let W1 := bpe3ub_W.map (bpe_full_merge 0 1 3)
  let E1 := bpe3ub_E.map (bpe_full_merge 0 1 3)
  let W2 := W1.map (bpe_full_merge 2 2 4)
  let E2 := E1.map (bpe_full_merge 2 2 4)
  let W3 := W2.map (bpe_full_merge 1 4 5)
  let E3 := E2.map (bpe_full_merge 1 4 5)
  refine ⟨bpe3ub_sepJoin 10 (bpe3ub_blocks n bpe3ub_W bpe3ub_E),
    bpe3ub_sepJoin 10 (bpe3ub_blocks n W3 E3), ?_, ?_, ?_⟩
  · refine ⟨_, bpe3ub_greedy n (4 * n + 1) 0 1 3 bpe3ub_W bpe3ub_E (by omega)
      (by norm_num) (by norm_num) (by norm_num) (by decide) (by decide) (by decide)
      (by decide) ?_ ?_, _, bpe3ub_greedy n (2 * n + 1) 2 2 4 W1 E1 (by omega)
      (by norm_num) (by norm_num) (by norm_num) (by decide) (by decide) (by decide)
      (by decide) ?_ ?_, _, bpe3ub_greedy n n 1 4 5 W2 E2 hn
      (by norm_num) (by norm_num) (by norm_num) (by decide) (by decide) (by decide)
      (by decide) ?_ ?_, rfl⟩
    · have key : ∀ a < 10, ∀ b < 10, (bpe3ub_W.map (bpe_pair_count a b)).sum ≤ 4 ∧
          (bpe3ub_E.map (bpe_pair_count a b)).sum ≤ 1 := by decide
      intro a ha b hb
      obtain ⟨h1, h2⟩ := key a ha b hb
      have := Nat.mul_le_mul_left n h1
      omega
    · have h1 : (bpe3ub_W.map (bpe_pair_count 0 1)).sum = 4 := by decide
      have h2 : (bpe3ub_E.map (bpe_pair_count 0 1)).sum = 1 := by decide
      rw [h1, h2]; ring
    · have key : ∀ a < 10, ∀ b < 10, (W1.map (bpe_pair_count a b)).sum ≤ 2 ∧
          (E1.map (bpe_pair_count a b)).sum ≤ 1 := by decide
      intro a ha b hb
      obtain ⟨h1, h2⟩ := key a ha b hb
      have := Nat.mul_le_mul_left n h1
      omega
    · have h1 : (W1.map (bpe_pair_count 2 2)).sum = 2 := by decide
      have h2 : (E1.map (bpe_pair_count 2 2)).sum = 1 := by decide
      rw [h1, h2]; ring
    · have key : ∀ a < 10, ∀ b < 10, (W2.map (bpe_pair_count a b)).sum ≤ 1 ∧
          (E2.map (bpe_pair_count a b)).sum = 0 := by decide
      intro a ha b hb
      obtain ⟨h1, h2⟩ := key a ha b hb
      have := Nat.mul_le_mul_left n h1
      omega
    · have h1 : (W2.map (bpe_pair_count 1 4)).sum = 1 := by decide
      have h2 : (E2.map (bpe_pair_count 1 4)).sum = 0 := by decide
      rw [h1, h2]; ring
  · let P1 := bpe3ub_W.map (bpe_full_merge 1 0 6)
    let Q1 := bpe3ub_E.map (bpe_full_merge 1 0 6)
    let P2 := P1.map (bpe_full_merge 1 2 7)
    let Q2 := Q1.map (bpe_full_merge 1 2 7)
    let P3 := P2.map (bpe_full_merge 2 0 8)
    let Q3 := Q2.map (bpe_full_merge 2 0 8)
    have hsteps : bpe_steps bpe_partial_step 3
        (bpe3ub_sepJoin 10 (bpe3ub_blocks n bpe3ub_W bpe3ub_E))
        (bpe3ub_sepJoin 10 (bpe3ub_blocks n P3 Q3)) :=
      ⟨_, bpe3ub_partial n 1 0 6 bpe3ub_W bpe3ub_E (by norm_num) (by norm_num)
          (by norm_num) (by decide) (by decide),
        _, bpe3ub_partial n 1 2 7 P1 Q1 (by norm_num) (by norm_num)
          (by norm_num) (by decide) (by decide),
        _, bpe3ub_partial n 2 0 8 P2 Q2 (by norm_num) (by norm_num)
          (by norm_num) (by decide) (by decide), rfl⟩
    have hlen : (bpe3ub_sepJoin 10 (bpe3ub_blocks n bpe3ub_W bpe3ub_E)).length -
        (bpe3ub_sepJoin 10 (bpe3ub_blocks n P3 Q3)).length = 12 * n := by
      rw [bpe3ub_len, bpe3ub_len]
      have e1 : (bpe3ub_W.map List.length).sum + bpe3ub_W.length = 30 := by decide
      have e2 : (bpe3ub_E.map List.length).sum + bpe3ub_E.length = 6 := by decide
      have e3 : (P3.map List.length).sum + P3.length = 18 := by decide
      have e4 : (Q3.map List.length).sum + Q3.length = 6 := by decide
      rw [e1, e2, e3, e4]; omega
    unfold bpe_optimal_utility
    apply le_csSup
    · refine ⟨(bpe3ub_sepJoin 10 (bpe3ub_blocks n bpe3ub_W bpe3ub_E)).length, ?_⟩
      rintro u ⟨t, _, rfl⟩
      omega
    · exact ⟨_, hsteps, hlen.symm⟩
  · rw [bpe3ub_len, bpe3ub_len]
    have e1 : (bpe3ub_W.map List.length).sum + bpe3ub_W.length = 30 := by decide
    have e2 : (bpe3ub_E.map List.length).sum + bpe3ub_E.length = 6 := by decide
    have e3 : (W3.map List.length).sum + W3.length = 23 := by decide
    have e4 : (E3.map List.length).sum + E3.length = 4 := by decide
    rw [e1, e2, e3, e4]; omega

theorem bpe_worst_case_ratio_three_upper_bound : bpe_worst_ratio 3 ≤ (7 : ℝ) / 12 := by
  have hbdd : BddBelow {r : ℝ | ∃ s t : List ℕ, bpe_steps bpe_greedy_step 3 s t ∧
      0 < bpe_optimal_utility s 3 ∧
      r = ((s.length - t.length : ℕ) : ℝ) / bpe_optimal_utility s 3} := by
    refine ⟨0, ?_⟩
    rintro r ⟨s, t, _, _, rfl⟩
    positivity
  have hn : ∀ n : ℕ, 1 ≤ n → bpe_worst_ratio 3 ≤ ((7 * n + 2 : ℕ) : ℝ) / (12 * n : ℕ) := by
    intro n hn
    obtain ⟨s, t, hst, hopt, hlen⟩ := bpe3ub_instance n hn
    have hpos : 0 < bpe_optimal_utility s 3 := by omega
    have h1 : bpe_worst_ratio 3 ≤ ((s.length - t.length : ℕ) : ℝ) / bpe_optimal_utility s 3 :=
      csInf_le hbdd ⟨s, t, hst, hpos, rfl⟩
    rw [hlen] at h1
    refine h1.trans ?_
    apply div_le_div_of_nonneg_left (by positivity) (by positivity)
    exact_mod_cast hopt
  by_contra hcon
  push Not at hcon
  obtain ⟨n, hn1⟩ := exists_nat_gt (1 / (bpe_worst_ratio 3 - 7 / 12))
  have hd : 0 < bpe_worst_ratio 3 - 7 / 12 := by linarith
  have hnpos : (0 : ℝ) < n := lt_trans (by positivity) hn1
  have hn1' : 1 ≤ n := by exact_mod_cast hnpos
  have h := hn n hn1'
  push_cast at h
  have : 1 < (n : ℝ) * (bpe_worst_ratio 3 - 7 / 12) := by
    rwa [div_lt_iff₀ hd] at hn1
  rw [le_div_iff₀ (by positivity)] at h
  nlinarith
