import AFTD.Prelude

/-!
# prioritized_borel_threshold_maximum_even_frequently

Topic: automata   Node: a550e281d490

Provenance: helper lemma. arXiv:2611.10136, Section 5.3.2, Proposition 41; s+1-state threshold controller for the paper’s lower-bound game.

If a positive index I occurs arbitrarily late and all sufficiently late inputs are at most I, then under the threshold update there are arbitrarily late occurrences of I at which the memory is below I.
-/

theorem prioritized_borel_threshold_maximum_even_frequently
    (f m : ℕ → ℕ) (I N0 : ℕ) (hI : 0 < I)
    (hmax : ∀ n, N0 ≤ n → f n ≤ I)
    (hinf : ∀ N, ∃ n ≥ N, f n = I)
    (hstep : ∀ n, m (n+1) = if m n < f n then f n else 0) :
    ∀ K, ∃ n ≥ K, f n = I ∧ m n < I := by
  intro K
  by_contra h
  push_neg at h
  obtain ⟨n, hn, hfn⟩ := hinf (max K N0)
  have hnK : K ≤ n := le_trans (le_max_left ..) hn
  have hnN : N0 ≤ n := le_trans (le_max_right ..) hn
  have hmn : I ≤ m n := by
    have := h n hnK hfn
    omega
  have hreset : m (n+1) = 0 := by
    rw [hstep, if_neg]
    omega
  have hind : ∀ j, m (n+1+j) < I := by
    intro j
    induction j with
    | zero => simpa using (show m (n+1) < I by rw [hreset]; exact hI)
    | succ j ih =>
      have hk : K ≤ n+1+j := by omega
      have hn0 : N0 ≤ n+1+j := by omega
      have hsmall : f (n+1+j) < I := by
        have hle := hmax (n+1+j) hn0
        have hne : f (n+1+j) ≠ I := by
          intro heq
          have := h (n+1+j) hk heq
          omega
        omega
      have hnext : m ((n+1+j)+1) < I := by
        rw [hstep]
        split_ifs <;> omega
      simpa [Nat.add_assoc] using hnext
  obtain ⟨n2, hn2, hfn2⟩ := hinf (n+1)
  have hn2K : K ≤ n2 := by omega
  have hm2 := hind (n2-(n+1))
  have heq : n+1+(n2-(n+1)) = n2 := by omega
  rw [heq] at hm2
  have := h n2 hn2K hfn2
  omega
