import AFTD.Prelude

/-!
# op309_cyclic_matching_domination_period_three

Topic: graphs   Node: 638e81c9226c

Provenance: helper lemma. Combinatorial cycle lemma for the OP-309 two-colors-per-perfect-matching obstruction; checked by SAT for lengths 1 through 100 in experiment 33558.

For a Boolean matching pattern on a cyclic sequence, if each position has a neighboring boundary position with exactly one matching edge adjacent to it, then the matching pattern is three-periodic and the cycle length is divisible by three.
-/

set_option maxRecDepth 8192

theorem op309_cycle_boundary_period
    (n : ℕ) [NeZero n] (m : ZMod n → Bool)
    (hmatch : ∀ i, m i = true → m (i + 1) = false)
    (hdom : ∀ i, m (i - 2) ≠ m i ∨ m i ≠ m (i + 2)) :
    ∀ i, m (i + 3) = m i := by
  have forward : ∀ i, m i = true → m (i + 3) = true := by
    intro i hi
    have hp : m (i - 1) = false := by
      cases h : m (i - 1) with
      | false => rfl
      | true =>
        have hh := hmatch (i - 1) h
        have hid : (i - 1) + 1 = i := by ring
        rw [hid, hi] at hh
        contradiction
    have hn : m (i + 1) = false := hmatch i hi
    have hh := hdom (i + 1)
    have hid1 : (i + 1) - 2 = i - 1 := by ring
    have hid2 : (i + 1) + 2 = i + 3 := by ring
    rw [hid1, hid2, hp, hn] at hh
    cases h : m (i + 3) <;> simp_all
  have backward : ∀ i, m i = true → m (i - 3) = true := by
    intro i hi
    have hp : m (i - 1) = false := by
      cases h : m (i - 1) with
      | false => rfl
      | true =>
        have hh := hmatch (i - 1) h
        have hid : (i - 1) + 1 = i := by ring
        rw [hid, hi] at hh
        contradiction
    have hn : m (i + 1) = false := hmatch i hi
    have hh := hdom (i - 1)
    have hid1 : (i - 1) - 2 = i - 3 := by ring
    have hid2 : (i - 1) + 2 = i + 1 := by ring
    rw [hid1, hid2, hp, hn] at hh
    cases h : m (i - 3) <;> simp_all
  intro i
  cases hi : m i with
  | false =>
    cases hj : m (i + 3) with
    | false => rfl
    | true =>
      have h := backward (i + 3) hj
      have hid : (i + 3) - 3 = i := by ring
      rw [hid, hi] at h
      contradiction
  | true => exact forward i hi

theorem op309_cyclic_matching_domination_period_three
    (n : ℕ) [NeZero n] (m : ZMod n → Bool)
    (hmatch : ∀ i, m i = true → m (i + 1) = false)
    (hdom : ∀ i, m (i - 2) ≠ m i ∨ m i ≠ m (i + 2)) :
    (∀ i, m (i + 3) = m i) ∧ 3 ∣ n := by
  have period : ∀ i, m (i + 3) = m i :=
    op309_cycle_boundary_period n m hmatch hdom
  constructor
  · exact period
  · by_contra hdiv
    have hcop : Nat.Coprime 3 n := (Nat.prime_three.coprime_iff_not_dvd).2 hdiv
    have hu : IsUnit (3 : ZMod n) := (ZMod.isUnit_iff_coprime 3 n).2 hcop
    obtain ⟨u, hu⟩ := hu
    let k : ℕ := (↑u⁻¹ : ZMod n).val
    have hk : (k : ZMod n) * 3 = 1 := by
      dsimp [k]
      rw [ZMod.natCast_zmod_val, ← hu]
      simp
    have hiter (i : ZMod n) : ∀ j : ℕ, m (i + (j : ZMod n) * 3) = m i := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        have hid : i + ((Nat.succ j : ℕ) : ZMod n) * 3 =
            (i + (j : ZMod n) * 3) + 3 := by push_cast; ring
        rw [hid, period, ih]
    have hstep (i : ZMod n) : m (i + 1) = m i := by
      simpa [hk] using hiter i k
    have hzero : ∀ i, m i = false := by
      intro i
      cases hi : m i with
      | false => rfl
      | true =>
        have hnext := hmatch i hi
        have heq := hstep i
        rw [hnext, hi] at heq
        contradiction
    have hh := hdom 0
    simp [hzero] at hh
