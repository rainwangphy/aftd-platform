import AFTD.Prelude
import AFTD.Kb.NumberTheory.HalvingPartitionCount
import AFTD.Kb.NumberTheory.IsHalvingPartition

/-!
# halving_partition_count_two_mul

Topic: elementary_number_theory   Node: 5ffcb1fed33f

Provenance: formalization of a published result. Source: arXiv:2611.01243 Lemma 2

For every natural number n, the number of halving partitions of 2n equals the number of halving partitions of n, that is, halving_partition_count (2 * n) = halving_partition_count n.
-/

private theorem halving_partition_count_two_mul_cons_mem (n : ℕ) (p : List ℕ)
    (hn : 0 < n) (hp : is_halving_partition n p) :
    is_halving_partition (2*n) (n :: p) := by
  unfold is_halving_partition at hp ⊢
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hn
    · exact hp.1 x hx
  · simp only [List.sum_cons, hp.2.1]
    omega
  · change (n = 2*n/2 ∨ n = (2*n+1)/2) ∧
      List.IsChain (fun x y => y = x/2 ∨ y = (x+1)/2) (n :: p)
    refine ⟨by omega, ?_⟩
    cases p with
    | nil => exact List.IsChain.singleton n
    | cons q tail =>
      obtain ⟨hq, hchain⟩ := hp.2.2
      exact List.IsChain.cons_cons hq hchain

private theorem halving_partition_count_two_mul_exists (n : ℕ) (q : List ℕ) (hn : 0 < n)
    (hq : is_halving_partition (2*n) q) :
    ∃ p, is_halving_partition n p ∧ q = n :: p := by
  unfold is_halving_partition at hq
  rcases hq with ⟨hpos, hsum, hmatch⟩
  cases q with
  | nil => simp at hmatch; omega
  | cons q1 tail =>
    obtain ⟨hq1, hchain⟩ := hmatch
    have hq1n : q1 = n := by
      rcases hq1 with h | h <;> omega
    simp only [List.sum_cons] at hsum
    have htailsum : tail.sum = n := by omega
    have htailne : tail ≠ [] := by
      intro h; subst h; simp at htailsum; omega
    cases tail with
    | nil => exact absurd rfl htailne
    | cons q2 tail2 =>
      rw [hq1n] at hchain
      have hR : (fun x y => y = x/2 ∨ y = (x+1)/2) n q2 :=
        List.IsChain.rel (R := fun x y => y = x/2 ∨ y = (x+1)/2) hchain
      have hchain' : List.IsChain (fun x y => y = x/2 ∨ y = (x+1)/2) (q2 :: tail2) :=
        (List.isChain_cons_cons.mp hchain).2
      refine ⟨q2 :: tail2, ?_, ?_⟩
      · unfold is_halving_partition
        exact ⟨by intro x hx; exact hpos x (List.mem_cons_of_mem _ hx), htailsum, hR, hchain'⟩
      · simp [hq1n]

/-- For every natural number n, the number of halving partitions of 2n equals the number of halving partitions of n. -/
theorem halving_partition_count_two_mul (n : ℕ) :
    halving_partition_count (2 * n) = halving_partition_count n := by
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    rfl
  · unfold halving_partition_count
    symm
    refine Set.ncard_congr (fun p _ => n :: p) ?_ ?_ ?_
    · intro p hp
      exact halving_partition_count_two_mul_cons_mem n p hn hp
    · intro p q hp hq h
      exact (List.cons.inj h).2
    · intro q hq
      obtain ⟨p, hp, hpq⟩ := halving_partition_count_two_mul_exists n q hn hq
      exact ⟨p, hp, hpq.symm⟩
