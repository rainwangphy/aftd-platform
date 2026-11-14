import AFTD.Prelude
import AFTD.Kb.Tcs.BpeMinGreedyUtility
import AFTD.Kb.Tcs.BpeOptimalFullUtility
import AFTD.Kb.Tcs.BpeFullStep
import AFTD.Kb.Tcs.BpeSteps
import AFTD.Kb.Tcs.BpeMaxPairCount
import AFTD.Kb.Tcs.BpeGreedyStep
import AFTD.Kb.Tcs.BpeFullMerge
import AFTD.Kb.Tcs.BpePairCount

/-!
# bpe_min_greedy_utility_one_eq_optimal

Topic: algorithms   Node: 0abd7ce77e13

Provenance: helper lemma. arXiv:2411.08671 Greedy Byte-Pair Encoding Achieves at Least 0.361 of the Optimal Compression, line 811

For any string s and merge budget k = 1, the minimum reduction in length achieved by a greedy full-merge step equals the optimal reduction achievable by any full-merge step.
-/

private lemma bpe_min_greedy_utility_one_eq_optimal_merge_length_le
    (a b z : ℕ) (s : List ℕ) : (bpe_full_merge a b z s).length ≤ s.length := by
  refine bpe_full_merge.induct a b (fun s => (bpe_full_merge a b z s).length ≤ s.length) ?_ ?_ ?_ ?_ s
  · simp [bpe_full_merge]
  · intro x
    simp [bpe_full_merge]
  · intro x y xs hxy ih
    have hm : bpe_full_merge a b z (x :: y :: xs) = z :: bpe_full_merge a b z xs := by
      simp [bpe_full_merge, hxy]
    rw [hm]
    simp only [List.length_cons] at ih ⊢
    omega
  · intro x y xs hxy ih
    have hm : bpe_full_merge a b z (x :: y :: xs) = x :: bpe_full_merge a b z (y :: xs) := by
      simp [bpe_full_merge, hxy]
    rw [hm]
    simp only [List.length_cons] at ih ⊢
    omega

private lemma bpe_min_greedy_utility_one_eq_optimal_merge_length_sub
    (a b z : ℕ) (s : List ℕ) :
    s.length - (bpe_full_merge a b z s).length = bpe_pair_count a b s := by
  refine bpe_full_merge.induct a b (fun s => s.length - (bpe_full_merge a b z s).length = bpe_pair_count a b s) ?_ ?_ ?_ ?_ s
  · simp [bpe_full_merge, bpe_pair_count]
  · intro x
    simp [bpe_full_merge, bpe_pair_count]
  · intro x y xs hxy ih
    have hm : bpe_full_merge a b z (x :: y :: xs) = z :: bpe_full_merge a b z xs := by
      simp [bpe_full_merge, hxy]
    have hc : bpe_pair_count a b (x :: y :: xs) = 1 + bpe_pair_count a b xs := by
      simp [bpe_pair_count, hxy]
    rw [hm, hc]
    simp only [List.length_cons] at ih ⊢
    have hle := bpe_min_greedy_utility_one_eq_optimal_merge_length_le a b z xs
    omega
  · intro x y xs hxy ih
    have hm : bpe_full_merge a b z (x :: y :: xs) = x :: bpe_full_merge a b z (y :: xs) := by
      simp [bpe_full_merge, hxy]
    have hc : bpe_pair_count a b (x :: y :: xs) = bpe_pair_count a b (y :: xs) := by
      simp [bpe_pair_count, hxy]
    rw [hm, hc]
    simp only [List.length_cons] at ih ⊢
    have hle := bpe_min_greedy_utility_one_eq_optimal_merge_length_le a b z (y :: xs)
    simp only [List.length_cons] at hle
    omega

private lemma bpe_min_greedy_utility_one_eq_optimal_pair_count_pos_mem_zip
    (a b : ℕ) (s : List ℕ) (h : 0 < bpe_pair_count a b s) :
    (a, b) ∈ s.zip s.tail := by
  refine bpe_pair_count.induct a b (fun s => 0 < bpe_pair_count a b s → (a, b) ∈ s.zip s.tail) ?_ ?_ ?_ ?_ s h
  · simp [bpe_pair_count]
  · intro x
    simp [bpe_pair_count]
  · intro x y xs hxy _ _
    simp [hxy]
  · intro x y xs hxy ih hpos
    have hc : bpe_pair_count a b (x :: y :: xs) = bpe_pair_count a b (y :: xs) := by
      simp [bpe_pair_count, hxy]
    rw [hc] at hpos
    have hmem := ih hpos
    simp only [List.zip_cons_cons, List.tail_cons]
    exact List.mem_cons_of_mem _ hmem

private lemma bpe_min_greedy_utility_one_eq_optimal_pair_count_le_max
    (a b : ℕ) (s : List ℕ) : bpe_pair_count a b s ≤ bpe_max_pair_count s := by
  rcases Nat.eq_zero_or_pos (bpe_pair_count a b s) with h0 | hpos
  · rw [h0]; exact Nat.zero_le _
  · have hmem := bpe_min_greedy_utility_one_eq_optimal_pair_count_pos_mem_zip a b s hpos
    have hle := Finset.le_sup (s := (s.zip s.tail).toFinset)
      (f := fun p : ℕ × ℕ => bpe_pair_count p.1 p.2 s) (by simpa using hmem)
    simpa [bpe_max_pair_count] using hle

private lemma bpe_min_greedy_utility_one_eq_optimal_exists_pair_eq_max
    (s : List ℕ) (h : 0 < bpe_max_pair_count s) :
    ∃ a b : ℕ, bpe_pair_count a b s = bpe_max_pair_count s := by
  have hne : (s.zip s.tail).toFinset.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro he
    rw [bpe_max_pair_count, he, Finset.sup_empty] at h
    exact absurd h (Nat.lt_irrefl 0)
  obtain ⟨p, hp, hsup⟩ := Finset.exists_mem_eq_sup _ hne (fun p : ℕ × ℕ => bpe_pair_count p.1 p.2 s)
  exact ⟨p.1, p.2, by simpa [bpe_max_pair_count] using hsup.symm⟩

private lemma bpe_min_greedy_utility_one_eq_optimal_exists_fresh (s : List ℕ) :
    ∃ z : ℕ, z ∉ s := by
  refine ⟨s.sum + 1, ?_⟩
  intro hz
  have hle := List.le_sum_of_mem hz
  omega

private lemma bpe_min_greedy_utility_one_eq_optimal_greedy_sub_eq_max
    (s t : List ℕ) (h : bpe_greedy_step s t) :
    s.length - t.length = bpe_max_pair_count s := by
  rcases h with ⟨hmax, rfl⟩ | ⟨a, b, z, hpos, hcount, hz, rfl⟩
  · simp [hmax]
  · rw [bpe_min_greedy_utility_one_eq_optimal_merge_length_sub, hcount]

private lemma bpe_min_greedy_utility_one_eq_optimal_full_sub_le_max
    (s t : List ℕ) (h : bpe_full_step s t) :
    s.length - t.length ≤ bpe_max_pair_count s := by
  rcases h with rfl | ⟨a, b, z, hz, rfl⟩
  · simp
  · rw [bpe_min_greedy_utility_one_eq_optimal_merge_length_sub]
    exact bpe_min_greedy_utility_one_eq_optimal_pair_count_le_max a b s

private lemma bpe_min_greedy_utility_one_eq_optimal_exists_greedy_step
    (s : List ℕ) :
    ∃ t : List ℕ, bpe_greedy_step s t ∧ s.length - t.length = bpe_max_pair_count s := by
  rcases Nat.eq_zero_or_pos (bpe_max_pair_count s) with h0 | hpos
  · refine ⟨s, Or.inl ⟨h0, rfl⟩, ?_⟩
    simp [h0]
  · obtain ⟨a, b, hab⟩ := bpe_min_greedy_utility_one_eq_optimal_exists_pair_eq_max s hpos
    obtain ⟨z, hz⟩ := bpe_min_greedy_utility_one_eq_optimal_exists_fresh s
    refine ⟨bpe_full_merge a b z s, Or.inr ⟨a, b, z, hpos, hab, hz, rfl⟩, ?_⟩
    rw [bpe_min_greedy_utility_one_eq_optimal_merge_length_sub, hab]

private lemma bpe_min_greedy_utility_one_eq_optimal_exists_full_step
    (s : List ℕ) :
    ∃ t : List ℕ, bpe_full_step s t ∧ s.length - t.length = bpe_max_pair_count s := by
  rcases Nat.eq_zero_or_pos (bpe_max_pair_count s) with h0 | hpos
  · refine ⟨s, Or.inl rfl, ?_⟩
    simp [h0]
  · obtain ⟨a, b, hab⟩ := bpe_min_greedy_utility_one_eq_optimal_exists_pair_eq_max s hpos
    obtain ⟨z, hz⟩ := bpe_min_greedy_utility_one_eq_optimal_exists_fresh s
    refine ⟨bpe_full_merge a b z s, Or.inr ⟨a, b, z, hz, rfl⟩, ?_⟩
    rw [bpe_min_greedy_utility_one_eq_optimal_merge_length_sub, hab]

/-- For merge budget k = 1, greedy utility equals optimal full-merge utility on any string. -/
theorem bpe_min_greedy_utility_one_eq_optimal (s : List ℕ) :
    bpe_min_greedy_utility s 1 = bpe_optimal_full_utility s 1 := by
  classical
  unfold bpe_min_greedy_utility bpe_optimal_full_utility
  have hG : {u : ℕ | ∃ t, bpe_steps bpe_greedy_step 1 s t ∧ u = s.length - t.length}
      = {u : ℕ | ∃ t, bpe_greedy_step s t ∧ u = s.length - t.length} := by
    ext u; simp [bpe_steps]
  have hF : {u : ℕ | ∃ t, bpe_steps bpe_full_step 1 s t ∧ u = s.length - t.length}
      = {u : ℕ | ∃ t, bpe_full_step s t ∧ u = s.length - t.length} := by
    ext u; simp [bpe_steps]
  rw [hG, hF]
  have hinf : sInf {u : ℕ | ∃ t, bpe_greedy_step s t ∧ u = s.length - t.length}
      = bpe_max_pair_count s := by
    have hne : ({u : ℕ | ∃ t, bpe_greedy_step s t ∧ u = s.length - t.length} : Set ℕ).Nonempty := by
      obtain ⟨t, ht, hut⟩ := bpe_min_greedy_utility_one_eq_optimal_exists_greedy_step s
      exact ⟨_, t, ht, hut.symm⟩
    have hmem := Nat.sInf_mem hne
    simp only [Set.mem_ofPred_eq] at hmem
    obtain ⟨t, ht, heq⟩ := hmem
    rw [heq]
    exact bpe_min_greedy_utility_one_eq_optimal_greedy_sub_eq_max s t ht
  have hsup : sSup {u : ℕ | ∃ t, bpe_full_step s t ∧ u = s.length - t.length}
      = bpe_max_pair_count s := by
    have hMmem : bpe_max_pair_count s ∈ {u : ℕ | ∃ t, bpe_full_step s t ∧ u = s.length - t.length} := by
      obtain ⟨t, ht, hut⟩ := bpe_min_greedy_utility_one_eq_optimal_exists_full_step s
      exact ⟨t, ht, hut.symm⟩
    have hbdd : ∃ n : ℕ, ∀ a ∈ {u : ℕ | ∃ t, bpe_full_step s t ∧ u = s.length - t.length}, a ≤ n := by
      refine ⟨bpe_max_pair_count s, ?_⟩
      intro a ha
      obtain ⟨t, ht, rfl⟩ := ha
      exact bpe_min_greedy_utility_one_eq_optimal_full_sub_le_max s t ht
    apply le_antisymm
    · rw [Nat.sSup_def hbdd]
      exact Nat.find_min' hbdd (fun a ha => by
        obtain ⟨t, ht, rfl⟩ := ha
        exact bpe_min_greedy_utility_one_eq_optimal_full_sub_le_max s t ht)
    · rw [Nat.sSup_def hbdd]
      exact Nat.find_spec hbdd _ hMmem
  rw [hinf, hsup]
