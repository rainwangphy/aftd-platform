import AFTD.Prelude

/-!
# prioritized_borel_highest_recurrent_index

Topic: automata   Node: bc10cbfd046a

Provenance: helper lemma. arXiv:2611.10136, Section 5.3.2, Proposition 41; threshold controller for the lower-bound example

Every infinite sequence of positive natural numbers bounded by s has a positive largest recurrent value I, and all sufficiently late values are at most I.
-/

theorem prioritized_borel_highest_recurrent_index (s : ℕ) (f : ℕ → ℕ)
    (hf : ∀ n, 1 ≤ f n ∧ f n ≤ s) :
    ∃ I, 0 < I ∧ I ≤ s ∧ (∀ N, ∃ n ≥ N, f n = I) ∧
      ∃ N0, ∀ n, N0 ≤ n → f n ≤ I := by
  classical
  let P : ℕ → Prop := fun i => ∀ N, ∃ n ≥ N, f n = i
  have hall : ∀ᶠ n in Filter.atTop, ∃ i ∈ Finset.range (s+1), f n = i := by
    filter_upwards [] with n
    exact ⟨f n, Finset.mem_range.mpr (by have := (hf n).2; omega), rfl⟩
  have hfre := (Filter.frequently_exists_finset (Finset.range (s+1))).mp hall.frequently
  obtain ⟨j, hj, hrec⟩ := hfre
  have hjbound : j ≤ s := by have := Finset.mem_range.mp hj; omega
  have hjrec : P j := Filter.frequently_atTop.mp hrec
  let I := Nat.findGreatest P s
  have hIrec : P I := Nat.findGreatest_spec hjbound hjrec
  have hIbound : I ≤ s := Nat.findGreatest_le s
  obtain ⟨n, _, hn⟩ := hIrec 0
  have hIpos : 0 < I := by have := (hf n).1; omega
  refine ⟨I, hIpos, hIbound, hIrec, ?_⟩
  by_contra h
  push_neg at h
  have hbad : ∃ᶠ n in Filter.atTop, I < f n := Filter.frequently_atTop.mpr h
  have hbad' : ∃ᶠ n in Filter.atTop,
      ∃ i ∈ Finset.range (s+1), I < i ∧ f n = i := by
    apply hbad.mono
    intro n hn
    exact ⟨f n, Finset.mem_range.mpr (by have := (hf n).2; omega), hn, rfl⟩
  obtain ⟨k, hk, hkrec⟩ := (Filter.frequently_exists_finset (Finset.range (s+1))).mp hbad'
  have hkbound : k ≤ s := by have := Finset.mem_range.mp hk; omega
  have hkgt : I < k := by
    obtain ⟨n, _, hn⟩ := Filter.frequently_atTop.mp hkrec 0
    exact hn.1
  have hkP : P k := by
    intro N
    obtain ⟨n, hn, hnk⟩ := Filter.frequently_atTop.mp hkrec N
    exact ⟨n, hn, hnk.2⟩
  exact (Nat.findGreatest_is_greatest hkgt hkbound) hkP
