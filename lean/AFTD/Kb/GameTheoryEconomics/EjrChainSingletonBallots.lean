import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsEjrCommitteeIffCandidateSubsets
import AFTD.Kb.GameTheoryEconomics.ExistsPermWithPrefixEqTake
import AFTD.Kb.GameTheoryEconomics.EjrChainIffLevelSupporters
import AFTD.Kb.GameTheoryEconomics.IsEjrCommittee
import AFTD.Kb.Tcs.Weight

/-!
# ejr_chain_singleton_ballots

Topic: social_choice   Node: cc6948410476

Provenance: helper lemma. step towards ejr_committee_monotone_chain_exists

If every voter approves at most one candidate, then there is an ordering of the candidates every prefix of which is an EJR committee of the corresponding size.
-/

/-- Double counting: the total number of approvals, summed over candidates, is at most the number of voters when every ballot approves at most one candidate. -/
private lemma ejr_chain_singleton_ballots_sum_support_le {n m : ℕ} (A : Fin n → Finset (Fin m))
    (hA : ∀ i, (A i).card ≤ 1) :
    ∑ c : Fin m, (Finset.univ.filter fun i => c ∈ A i).card ≤ n := by
  classical
  have h1 : ∑ c : Fin m, (Finset.univ.filter fun i : Fin n => c ∈ A i).card
      = ∑ c : Fin m, ∑ i : Fin n, (if c ∈ A i then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro c _
    rw [Finset.sum_boole]
    simp
  rw [h1, Finset.sum_comm]
  have h2 : ∑ i : Fin n, ∑ c : Fin m, (if c ∈ A i then 1 else 0) = ∑ i : Fin n, (A i).card := by
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_boole]
    simp
  rw [h2]
  calc ∑ i : Fin n, (A i).card ≤ ∑ i : Fin n, 1 := Finset.sum_le_sum (fun i _ => hA i)
    _ = n := by simp

/-- Scheduling lemma: if the total weight `∑ s` is at most `n > 0`, the candidates can be
ordered so that a candidate `c` placed at 0-based position `σ c` satisfies `s c * σ c < n`;
sorting by non-increasing weight works. -/
private lemma ejr_chain_singleton_ballots_exists_perm {m n : ℕ} (s : Fin m → ℕ) (hn : 0 < n)
    (hsum : ∑ c, s c ≤ n) : ∃ σ : Equiv.Perm (Fin m), ∀ c, s c * (σ c : ℕ) < n := by
  classical
  set atPos : Equiv.Perm (Fin m) := Tuple.sort (fun c : Fin m => OrderDual.toDual (s c)) with hatPos
  have hmono : Monotone ((fun c : Fin m => OrderDual.toDual (s c)) ∘ atPos) := Tuple.monotone_sort _
  have hanti : Antitone (fun i : Fin m => s (atPos i)) := by
    intro a b hab
    exact OrderDual.toDual_le_toDual.mp (hmono hab)
  have key : ∀ c : Fin m, s c * ((atPos.symm c : Fin m) : ℕ) < n := by
    intro c
    set p : Fin m := atPos.symm c with hp
    have hpc : atPos p = c := by simp [hp]
    have hlt : (p : ℕ) < (Finset.univ.filter fun i : Fin m => s c ≤ s (atPos i)).card := by
      rw [Tuple.lt_card_ge_iff_apply_ge_of_antitone (f := fun i : Fin m => s (atPos i))
        (a := s c) (j := p) hanti]
      simp [hpc]
    have hcard : (Finset.univ.filter fun i : Fin m => s c ≤ s (atPos i)).card
        = (Finset.univ.filter fun x : Fin m => s c ≤ s x).card := by
      refine Finset.card_bij (fun i _ => atPos i) ?_ ?_ ?_
      · intro i hi
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2⟩
      · intro i _ j _ hij
        exact atPos.injective hij
      · intro b hb
        exact ⟨atPos.symm b,
          Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa using (Finset.mem_filter.mp hb).2⟩,
          by simp⟩
    have hbound : (Finset.univ.filter fun x : Fin m => s c ≤ s x).card * s c ≤ n := by
      have step1 : (Finset.univ.filter fun x : Fin m => s c ≤ s x).card * s c
          ≤ ∑ x ∈ Finset.univ.filter (fun x : Fin m => s c ≤ s x), s x := by
        have := Finset.card_nsmul_le_sum (Finset.univ.filter (fun x : Fin m => s c ≤ s x)) s (s c)
          (fun x hx => (Finset.mem_filter.mp hx).2)
        simpa [nsmul_eq_mul] using this
      have step2 : ∑ x ∈ Finset.univ.filter (fun x : Fin m => s c ≤ s x), s x ≤ ∑ x, s x :=
        Finset.sum_le_univ_sum_of_nonneg (fun x => Nat.zero_le _)
      exact le_trans step1 (le_trans step2 hsum)
    have hp1 : (p : ℕ) + 1 ≤ (Finset.univ.filter fun x : Fin m => s c ≤ s x).card := by omega
    have hle : s c * ((p : ℕ) + 1) ≤ n := by
      rw [Nat.mul_comm]
      exact le_trans (Nat.mul_le_mul_right (s c) hp1) hbound
    by_cases hsc : s c = 0
    · rw [hsc, Nat.zero_mul]; exact hn
    · have hpos : 0 < s c := Nat.pos_of_ne_zero hsc
      have hstrict : s c * (p : ℕ) < s c * ((p : ℕ) + 1) :=
        Nat.mul_lt_mul_of_pos_left (Nat.lt_succ_self _) hpos
      exact lt_of_lt_of_le hstrict hle
  exact ⟨atPos.symm, key⟩

/-- The chain target holds when every voter approves at most one candidate. -/
theorem ejr_chain_singleton_ballots {n m : ℕ} (A : Fin n → Finset (Fin m)) (hn : 0 < n)
    (hA : ∀ i, (A i).card ≤ 1) :
    ∃ σ : Equiv.Perm (Fin m), ∀ k, k ≤ m →
      is_ejr_committee A k (Finset.univ.filter fun c => (σ c : ℕ) < k) := by
  classical
  set s : Fin m → ℕ := fun c => (Finset.univ.filter fun i => c ∈ A i).card with hs
  have hsum : ∑ c, s c ≤ n := ejr_chain_singleton_ballots_sum_support_le A hA
  obtain ⟨σ, hσ⟩ := ejr_chain_singleton_ballots_exists_perm s hn hsum
  refine (ejr_chain_iff_level_supporters A).mpr ⟨σ, ?_⟩
  intro k hk T hT
  set W : Finset (Fin m) := Finset.univ.filter fun c => (σ c : ℕ) < k with hW
  rcases Nat.lt_or_ge T.card 2 with h2 | h2
  · have hT1 : T.card = 1 := by
      have hpos : 0 < T.card := Finset.card_pos.mpr hT
      omega
    obtain ⟨c, rfl⟩ := Finset.card_eq_one.mp hT1
    have hsupp : (Finset.univ.filter fun i => ({c} : Finset (Fin m)) ⊆ A i ∧ (A i ∩ W).card < 1)
        = Finset.univ.filter fun i => c ∈ A i ∧ c ∉ W := by
      apply Finset.filter_congr
      intro i _
      constructor
      · rintro ⟨hsub, hlt⟩
        refine ⟨hsub (Finset.mem_singleton_self c), ?_⟩
        intro hcW
        have hpos : 0 < (A i ∩ W).card :=
          Finset.card_pos.mpr ⟨c, Finset.mem_inter.mpr ⟨hsub (Finset.mem_singleton_self c), hcW⟩⟩
        omega
      · rintro ⟨hc, hcW⟩
        refine ⟨Finset.singleton_subset_iff.mpr hc, ?_⟩
        have hempty : ¬ (A i ∩ W).Nonempty := by
          rintro ⟨x, hx⟩
          obtain ⟨hxA, hxW⟩ := Finset.mem_inter.mp hx
          have hxc : x = c := Finset.card_le_one.mp (hA i) x hxA c hc
          exact hcW (hxc ▸ hxW)
        rw [Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hempty)]
        exact Nat.zero_lt_one
    rw [Finset.card_singleton, hsupp, Nat.one_mul]
    by_cases hcW : c ∈ W
    · have hempty : (Finset.univ.filter fun i : Fin n => c ∈ A i ∧ c ∉ W) = ∅ := by
        apply Finset.filter_false_of_mem
        intro i _ h
        exact h.2 hcW
      rw [hempty, Finset.card_empty, Nat.zero_mul]
      exact hn
    · have hksig : k ≤ (σ c : ℕ) := by
        rw [hW] at hcW
        simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_lt] at hcW
        exact hcW
      have hcard : (Finset.univ.filter fun i : Fin n => c ∈ A i ∧ c ∉ W).card ≤ s c := by
        rw [hs]
        apply Finset.card_le_card
        intro i hi
        exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hi).2.1⟩
      calc (Finset.univ.filter fun i : Fin n => c ∈ A i ∧ c ∉ W).card * k
          ≤ s c * k := Nat.mul_le_mul_right k hcard
        _ ≤ s c * (σ c : ℕ) := Nat.mul_le_mul_left (s c) hksig
        _ < n := hσ c
  · have hempty : (Finset.univ.filter fun i => T ⊆ A i ∧ (A i ∩ W).card < T.card) = ∅ := by
      apply Finset.filter_false_of_mem
      intro i _ h
      have h1 : T.card ≤ (A i).card := Finset.card_le_card h.1
      have h2 := hA i
      omega
    rw [hempty, Finset.card_empty, Nat.zero_mul]
    exact Nat.mul_pos (by omega) hn
