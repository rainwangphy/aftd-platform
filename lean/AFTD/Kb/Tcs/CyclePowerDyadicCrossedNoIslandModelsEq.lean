import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.CyclePowerExactPairUnique
import AFTD.Kb.Tcs.CyclePowerDyadicTightClassParent

/-!
# cycle_power_dyadic_crossed_no_island_models_eq

Topic: combinatorics   Node: 441279701f01

Provenance: helper lemma. RT-1 / OP-205 (arXiv:2610.15635, Theorems 1.3-1.4: eq(C_n^k) for k+1 = 2^m, n even, (k+1) not dividing n). Session 2026-11-08: the alignment lemma cycle_power_dyadic_no_island_of_alternating_halves reduced to the pairing of the two half models, which experiment 18632 finds forced already inside the span of one class.

Pairing conjecture for coupled no-island models. Let m ≥ 1 and let y, z : ℤ → ℕ → Bool be two integer Boolean class models at exponent m, each tight (every class has dyadic weight equal to its size) and exactly dyadically covered, and each without islands (no a < b < c < 2^m with bit a missing, bit b selected, bit c missing). Suppose they are crossed-covered: for every 1 ≤ j < m and every vertex v there is a < 2^j with y (v-a) a and z (v-a) (a+2^m-2^j), and there is a < 2^j with z (v-a) a and y (v-a) (a+2^m-2^j). Then y and z agree: y p a = z p a for every root p and every a < 2^m.
-/

theorem cycle_power_dyadic_crossed_parent_lo (m k : ℕ) (hk : k + 1 < m) (S : ℕ → Bool)
    (htight : cycle_power_dyadic_class_weight m S =
      (Finset.range (2^m)).sum (fun a => (S a).toNat))
    (a : ℕ) (ha : a < 2 ^ k) (h : S (a + 2 ^ m - 2 ^ (k + 1)) = true) : S a = true := by
  have hk2 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
  have := cycle_power_dyadic_tight_class_parent m (k + 1) (by omega) hk S htight a (by omega)
  simp only [Nat.add_sub_cancel] at this
  exact this.1 ha h

theorem cycle_power_dyadic_crossed_parent_hi (m k : ℕ) (hk : k + 1 < m) (S : ℕ → Bool)
    (htight : cycle_power_dyadic_class_weight m S =
      (Finset.range (2^m)).sum (fun a => (S a).toNat))
    (a : ℕ) (ha1 : 2 ^ k ≤ a) (ha2 : a < 2 ^ (k + 1)) (h : S a = true) :
    S (a + 2 ^ m - 2 ^ (k + 1)) = true := by
  have := cycle_power_dyadic_tight_class_parent m (k + 1) (by omega) hk S htight a ha2
  simp only [Nat.add_sub_cancel] at this
  exact this.2 ha1 h

/-- a selected offset lies in the initial or in the terminal run of a class without islands -/
theorem cycle_power_dyadic_crossed_run (m : ℕ) (S : ℕ → Bool)
    (hshape : ∀ (a b c : ℕ), a < b → b < c → c < 2^m →
      S a = false → S b = true → S c = true)
    (a : ℕ) (hSa : S a = true) :
    (∀ b ≤ a, S b = true) ∨ (∀ b, a ≤ b → b < 2 ^ m → S b = true) := by
  by_contra hcon
  push Not at hcon
  obtain ⟨⟨b1, hb1, h1⟩, ⟨b2, hb2, hb2', h2⟩⟩ := hcon
  have h1' : S b1 = false := by simpa using h1
  have h2' : S b2 = false := by simpa using h2
  have hne1 : b1 ≠ a := by
    rintro rfl; rw [hSa] at h1'; exact absurd h1' (by decide)
  have hne2 : b2 ≠ a := by
    rintro rfl; rw [hSa] at h2'; exact absurd h2' (by decide)
  have := hshape b1 a b2 (by omega) (by omega) hb2' h1' hSa
  rw [h2'] at this; exact absurd this (by decide)

/-- big suffix: offset `2^m - 2^i` selected (`i + 2 ≤ m`) forces `[2^m - 2^i, 2^m)` -/
theorem cycle_power_dyadic_crossed_big_suffix (m i : ℕ) (hi : i + 2 ≤ m) (S : ℕ → Bool)
    (htight : cycle_power_dyadic_class_weight m S =
      (Finset.range (2^m)).sum (fun a => (S a).toNat))
    (hshape : ∀ (a b c : ℕ), a < b → b < c → c < 2^m →
      S a = false → S b = true → S c = true)
    (hN : S (2^m - 2^i) = true) :
    ∀ b, 2^m - 2^i ≤ b → b < 2^m → S b = true := by
  have hm1 : 2 ^ m = 2 * 2 ^ (m - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hm2 : 2 ^ (m - 1) = 2 * 2 ^ (m - 2) := by
    rw [← pow_succ']; congr 1; omega
  have hii : 2 ^ i ≤ 2 ^ (m - 2) := Nat.pow_le_pow_right (by decide) (by omega)
  have hipos : 0 < 2 ^ i := Nat.two_pow_pos i
  intro c hc1 hc2
  by_contra hcf
  have hcf' : S c = false := by simpa using hcf
  have hcne : c ≠ 2 ^ m - 2 ^ i := by
    rintro rfl; rw [hN] at hcf'; exact absurd hcf' (by decide)
  have hpre : ∀ a < 2 ^ m - 2 ^ i, S a = true := by
    intro a ha
    by_contra haf
    have haf' : S a = false := by simpa using haf
    have := hshape a (2 ^ m - 2 ^ i) c ha (by omega) hc2 haf' hN
    rw [hcf'] at this; exact absurd this (by decide)
  have hpar := cycle_power_dyadic_crossed_parent_hi m (m - 2) (by omega) S htight
    (c - 2 ^ (m - 1)) (by omega) (by rw [show m - 2 + 1 = m - 1 by omega]; omega)
    (hpre _ (by omega))
  rw [show m - 2 + 1 = m - 1 by omega,
    show c - 2 ^ (m - 1) + 2 ^ m - 2 ^ (m - 1) = c by omega] at hpar
  rw [hpar] at hcf'; exact absurd hcf' (by decide)

/-- big prefix: offset `2^i - 1` selected (`i + 2 ≤ m`) forces `[0, 2^i)` -/
theorem cycle_power_dyadic_crossed_big_prefix (m i : ℕ) (hi : i + 2 ≤ m) (S : ℕ → Bool)
    (htight : cycle_power_dyadic_class_weight m S =
      (Finset.range (2^m)).sum (fun a => (S a).toNat))
    (hshape : ∀ (a b c : ℕ), a < b → b < c → c < 2^m →
      S a = false → S b = true → S c = true)
    (hP : S (2^i - 1) = true) :
    ∀ b < 2^i, S b = true := by
  have hm1 : 2 ^ m = 2 * 2 ^ (m - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hm2 : 2 ^ (m - 1) = 2 * 2 ^ (m - 2) := by
    rw [← pow_succ']; congr 1; omega
  have hii : 2 ^ i ≤ 2 ^ (m - 2) := Nat.pow_le_pow_right (by decide) (by omega)
  have hipos : 0 < 2 ^ i := Nat.two_pow_pos i
  intro b hb
  by_contra hbf
  have hbf' : S b = false := by simpa using hbf
  have hbne : b ≠ 2 ^ i - 1 := by
    rintro rfl; rw [hP] at hbf'; exact absurd hbf' (by decide)
  have hsuf : ∀ c, 2 ^ i - 1 < c → c < 2 ^ m → S c = true :=
    fun c hc1 hc2 => hshape b (2 ^ i - 1) c (by omega) hc1 hc2 hbf' hP
  have hpar := cycle_power_dyadic_crossed_parent_lo m (m - 2) (by omega) S htight b (by omega)
    (hsuf _ (by rw [show m - 2 + 1 = m - 1 by omega]; omega)
      (by rw [show m - 2 + 1 = m - 1 by omega]; omega))
  rw [hpar] at hbf'; exact absurd hbf' (by decide)

/-- a selected offset in `[2^k, 2^(k+1))` (`k + 1 < m`) forces the outer `2^k`-shell -/
theorem cycle_power_dyadic_crossed_shell_lo (m k : ℕ) (hk : k + 1 < m) (S : ℕ → Bool)
    (htight : cycle_power_dyadic_class_weight m S =
      (Finset.range (2^m)).sum (fun a => (S a).toNat))
    (hshape : ∀ (a b c : ℕ), a < b → b < c → c < 2^m →
      S a = false → S b = true → S c = true)
    (a : ℕ) (ha1 : 2 ^ k ≤ a) (ha2 : a < 2 ^ (k + 1)) (hSa : S a = true) :
    (∀ b < 2 ^ k, S b = true) ∧ (∀ b, 2 ^ m - 2 ^ k ≤ b → b < 2 ^ m → S b = true) := by
  have hm1 : 2 ^ m = 2 * 2 ^ (m - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hk1 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
  have hkm : 2 ^ (k + 1) ≤ 2 ^ (m - 1) := Nat.pow_le_pow_right (by decide) (by omega)
  rcases cycle_power_dyadic_crossed_run m S hshape a hSa with hpre | hsuf
  · refine ⟨fun b hb => hpre b (by omega), ?_⟩
    have hp := cycle_power_dyadic_crossed_parent_hi m k hk S htight (2 ^ k) le_rfl (by omega)
      (hpre _ ha1)
    rw [show 2 ^ k + 2 ^ m - 2 ^ (k + 1) = 2 ^ m - 2 ^ k by omega] at hp
    exact cycle_power_dyadic_crossed_big_suffix m k (by omega) S htight hshape hp
  · refine ⟨?_, fun b hb1 hb2 => hsuf b (by omega) hb2⟩
    intro b hb
    have hm2 : 2 ^ (m - 1) = 2 * 2 ^ (m - 2) := by
      rw [← pow_succ']; congr 1; omega
    have hkm2 : 2 ^ k ≤ 2 ^ (m - 2) := Nat.pow_le_pow_right (by decide) (by omega)
    exact cycle_power_dyadic_crossed_parent_lo m (m - 2) (by omega) S htight b (by omega)
      (hsuf _ (by rw [show m - 2 + 1 = m - 1 by omega]; omega)
        (by rw [show m - 2 + 1 = m - 1 by omega]; omega))

/-- a selected offset in `[2^m - 2^(k+1), 2^m - 2^k)` (`k + 1 < m`) forces the outer `2^k`-shell -/
theorem cycle_power_dyadic_crossed_shell_hi (m k : ℕ) (hk : k + 1 < m) (S : ℕ → Bool)
    (htight : cycle_power_dyadic_class_weight m S =
      (Finset.range (2^m)).sum (fun a => (S a).toNat))
    (hshape : ∀ (a b c : ℕ), a < b → b < c → c < 2^m →
      S a = false → S b = true → S c = true)
    (a : ℕ) (ha1 : 2 ^ m - 2 ^ (k + 1) ≤ a) (ha2 : a < 2 ^ m - 2 ^ k) (hSa : S a = true) :
    (∀ b < 2 ^ k, S b = true) ∧ (∀ b, 2 ^ m - 2 ^ k ≤ b → b < 2 ^ m → S b = true) := by
  have hm1 : 2 ^ m = 2 * 2 ^ (m - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hk1 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
  have hkm : 2 ^ (k + 1) ≤ 2 ^ (m - 1) := Nat.pow_le_pow_right (by decide) (by omega)
  have hm2 : 2 ^ (m - 1) = 2 * 2 ^ (m - 2) := by
    rw [← pow_succ']; congr 1; omega
  have hkm2 : 2 ^ k ≤ 2 ^ (m - 2) := Nat.pow_le_pow_right (by decide) (by omega)
  rcases cycle_power_dyadic_crossed_run m S hshape a hSa with hpre | hsuf
  · refine ⟨fun b hb => hpre b (by omega), ?_⟩
    intro b hb1 hb2
    have hp := cycle_power_dyadic_crossed_parent_hi m (m - 2) (by omega) S htight
      (b - 2 ^ (m - 1)) (by omega) (by rw [show m - 2 + 1 = m - 1 by omega]; omega)
      (hpre _ (by omega))
    rw [show m - 2 + 1 = m - 1 by omega,
      show b - 2 ^ (m - 1) + 2 ^ m - 2 ^ (m - 1) = b by omega] at hp
    exact hp
  · refine ⟨?_, fun b hb1 hb2 => hsuf b (by omega) hb2⟩
    have hp := cycle_power_dyadic_crossed_parent_lo m k hk S htight (2 ^ k - 1) (by omega)
      (by rw [show 2 ^ k - 1 + 2 ^ m - 2 ^ (k + 1) = 2 ^ m - 2 ^ k - 1 by omega]
          exact hsuf _ (by omega) (by omega))
    exact cycle_power_dyadic_crossed_big_prefix m k (by omega) S htight hshape hp

theorem cycle_power_dyadic_crossed_prefix_rule (m : ℕ) (y z : ℤ → ℕ → Bool)
    (ytight : ∀ p, cycle_power_dyadic_class_weight m (y p) =
      (Finset.range (2^m)).sum (fun a => (y p a).toNat))
    (ztight : ∀ p, cycle_power_dyadic_class_weight m (z p) =
      (Finset.range (2^m)).sum (fun a => (z p a).toNat))
    (yexact : ∀ j < m, ∀ v : ℤ, (Finset.range (2^j)).sum (fun a =>
      (y (v-(a : ℤ)) a && y (v-(a : ℤ)) (a+2^m-2^j)).toNat) = 1)
    (zexact : ∀ j < m, ∀ v : ℤ, (Finset.range (2^j)).sum (fun a =>
      (z (v-(a : ℤ)) a && z (v-(a : ℤ)) (a+2^m-2^j)).toNat) = 1)
    (yshape : ∀ (p : ℤ) (a b c : ℕ), a < b → b < c → c < 2^m →
      y p a = false → y p b = true → y p c = true)
    (hcross : ∀ j : ℕ, 1 ≤ j → j < m → ∀ v : ℤ,
      ∃ a : ℕ, a < 2^j ∧ y (v-(a : ℤ)) a = true ∧ z (v-(a : ℤ)) (a+2^m-2^j) = true)
    (p : ℤ) (L k : ℕ) (hk : k + 1 < m) (hL1 : 2 ^ k ≤ L) (hL2 : L < 2 ^ (k + 1))
    (hy0 : ∀ b < 2 ^ k, y p b = true) (hR : y p (2 ^ m - 2 ^ k) = true)
    (hyL : y p L = false) (hzL : z p L = true) :
    False := by
  have hk1 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
  have hjm' : 2 ^ (k + 1) < 2 ^ m := Nat.pow_lt_pow_right (by decide) hk
  have hkpos : 0 < 2 ^ k := Nat.two_pow_pos _
  obtain ⟨a, ha, hya, hzb⟩ := hcross (k + 1) (by omega) hk (p + L)
  rcases Nat.lt_or_ge a (2 ^ k) with hasmall | habig
  · have hza := cycle_power_dyadic_crossed_parent_lo m k hk _ (ztight (p + L - a)) a hasmall hzb
    have hzL2 := cycle_power_dyadic_crossed_parent_hi m k hk _ (ztight p) L hL1 hL2 hzL
    have hpL : p + (L : ℤ) - (L : ℤ) = p := by ring
    have := cycle_power_exact_pair_unique (2 ^ m) (2 ^ (k + 1)) z (zexact (k + 1) hk) (p + L)
      a L ha hL2 hza hzb (by rw [hpL]; exact hzL) (by rw [hpL]; exact hzL2)
    omega
  · have hane : a ≠ L := by
      rintro rfl
      rw [show p + (a : ℤ) - (a : ℤ) = p by ring, hyL] at hya
      exact absurd hya (by decide)
    have hq := cycle_power_dyadic_crossed_shell_lo m k hk _ (ytight (p + L - a))
      (yshape (p + L - a)) a habig ha hya
    have hsuf0 := cycle_power_dyadic_crossed_big_suffix m k (by omega) (y p) (ytight p)
      (yshape p) hR
    have hex := yexact k (by omega)
    rcases Nat.lt_or_ge a L with hal | hal
    · have hv : p + (L : ℤ) - (a : ℤ) = p + ((L - a : ℕ) : ℤ) := by push_cast [hal.le]; ring
      have h1 : p + ((L - a : ℕ) : ℤ) - ((L - a : ℕ) : ℤ) = p := by ring
      have h2 : p + ((L - a : ℕ) : ℤ) - ((0 : ℕ) : ℤ) = p + (L : ℤ) - (a : ℤ) := by
        rw [hv]; simp
      have := cycle_power_exact_pair_unique (2 ^ m) (2 ^ k) y hex (p + ((L - a : ℕ) : ℤ))
        (L - a) 0 (by omega) hkpos
        (by rw [h1]; exact hy0 _ (by omega))
        (by rw [h1]; exact hsuf0 _ (by omega) (by omega))
        (by rw [h2]; exact hq.1 0 hkpos)
        (by rw [h2]; exact hq.2 _ (by omega) (by omega))
      omega
    · have h1 : p - ((0 : ℕ) : ℤ) = p := by simp
      have h2 : p - ((a - L : ℕ) : ℤ) = p + (L : ℤ) - (a : ℤ) := by push_cast [hal]; ring
      have := cycle_power_exact_pair_unique (2 ^ m) (2 ^ k) y hex p
        0 (a - L) hkpos (by omega)
        (by rw [h1]; exact hy0 0 hkpos)
        (by rw [h1]; exact hsuf0 _ (by omega) (by omega))
        (by rw [h2]; exact hq.1 _ (by omega))
        (by rw [h2]; exact hq.2 _ (by omega) (by omega))
      omega

theorem cycle_power_dyadic_crossed_suffix_rule (m : ℕ) (y z : ℤ → ℕ → Bool)
    (ytight : ∀ p, cycle_power_dyadic_class_weight m (y p) =
      (Finset.range (2^m)).sum (fun a => (y p a).toNat))
    (ztight : ∀ p, cycle_power_dyadic_class_weight m (z p) =
      (Finset.range (2^m)).sum (fun a => (z p a).toNat))
    (yexact : ∀ j < m, ∀ v : ℤ, (Finset.range (2^j)).sum (fun a =>
      (y (v-(a : ℤ)) a && y (v-(a : ℤ)) (a+2^m-2^j)).toNat) = 1)
    (zexact : ∀ j < m, ∀ v : ℤ, (Finset.range (2^j)).sum (fun a =>
      (z (v-(a : ℤ)) a && z (v-(a : ℤ)) (a+2^m-2^j)).toNat) = 1)
    (yshape : ∀ (p : ℤ) (a b c : ℕ), a < b → b < c → c < 2^m →
      y p a = false → y p b = true → y p c = true)
    (hcross : ∀ j : ℕ, 1 ≤ j → j < m → ∀ v : ℤ,
      ∃ a : ℕ, a < 2^j ∧ z (v-(a : ℤ)) a = true ∧ y (v-(a : ℤ)) (a+2^m-2^j) = true)
    (p : ℤ) (c k : ℕ) (hk : k + 1 < m) (hc1 : 2 ^ m - 2 ^ (k + 1) ≤ c) (hc2 : c < 2 ^ m - 2 ^ k)
    (hy1 : ∀ b, 2 ^ m - 2 ^ k ≤ b → b < 2 ^ m → y p b = true) (hR : y p (2 ^ k - 1) = true)
    (hyc : y p c = false) (hzc : z p c = true) :
    False := by
  have hk1 : 2 ^ (k + 1) = 2 * 2 ^ k := by rw [pow_succ]; ring
  have hjm' : 2 ^ (k + 1) < 2 ^ m := Nat.pow_lt_pow_right (by decide) hk
  have hkpos : 0 < 2 ^ k := Nat.two_pow_pos _
  -- e = c - (2^m - 2^(k+1)) < 2^k
  obtain ⟨a, ha, hza, hyb⟩ := hcross (k + 1) (by omega) hk (p + ((c + 2 ^ (k + 1) - 2 ^ m : ℕ) : ℤ))
  set e := c + 2 ^ (k + 1) - 2 ^ m with he
  have hce : e + 2 ^ m - 2 ^ (k + 1) = c := by omega
  rcases Nat.lt_or_ge a (2 ^ k) with hasmall | habig
  · have hane : a ≠ e := by
      intro hae
      rw [hae, show p + (e : ℤ) - (e : ℤ) = p by ring, hce, hyc] at hyb
      exact absurd hyb (by decide)
    have hq := cycle_power_dyadic_crossed_shell_hi m k hk _ (ytight (p + e - a))
      (yshape (p + e - a)) (a + 2 ^ m - 2 ^ (k + 1)) (by omega) (by omega) hyb
    have hpre0 := cycle_power_dyadic_crossed_big_prefix m k (by omega) (y p) (ytight p)
      (yshape p) hR
    have hex := yexact k (by omega)
    rcases Nat.lt_or_ge a e with hal | hal
    · have hv : p + (e : ℤ) - (a : ℤ) = p + ((e - a : ℕ) : ℤ) := by push_cast [hal.le]; ring
      have h1 : p + ((e - a : ℕ) : ℤ) - ((e - a : ℕ) : ℤ) = p := by ring
      have h2 : p + ((e - a : ℕ) : ℤ) - ((0 : ℕ) : ℤ) = p + (e : ℤ) - (a : ℤ) := by
        rw [hv]; simp
      have := cycle_power_exact_pair_unique (2 ^ m) (2 ^ k) y hex (p + ((e - a : ℕ) : ℤ))
        (e - a) 0 (by omega) hkpos
        (by rw [h1]; exact hpre0 _ (by omega))
        (by rw [h1]; exact hy1 _ (by omega) (by omega))
        (by rw [h2]; exact hq.1 0 hkpos)
        (by rw [h2]; exact hq.2 _ (by omega) (by omega))
      omega
    · have h1 : p - ((0 : ℕ) : ℤ) = p := by simp
      have h2 : p - ((a - e : ℕ) : ℤ) = p + (e : ℤ) - (a : ℤ) := by push_cast [hal]; ring
      have := cycle_power_exact_pair_unique (2 ^ m) (2 ^ k) y hex p
        0 (a - e) hkpos (by omega)
        (by rw [h1]; exact hpre0 0 hkpos)
        (by rw [h1]; exact hy1 _ (by omega) (by omega))
        (by rw [h2]; exact hq.1 _ (by omega))
        (by rw [h2]; exact hq.2 _ (by omega) (by omega))
      omega
  · have hzb := cycle_power_dyadic_crossed_parent_hi m k hk _ (ztight (p + e - a)) a habig ha hza
    have hze := cycle_power_dyadic_crossed_parent_lo m k hk _ (ztight p) e (by omega)
      (by rw [hce]; exact hzc)
    have hpe : p + (e : ℤ) - (e : ℤ) = p := by ring
    have := cycle_power_exact_pair_unique (2 ^ m) (2 ^ (k + 1)) z (zexact (k + 1) hk) (p + e)
      a e ha (by omega) hza hzb (by rw [hpe]; exact hze) (by rw [hpe, hce]; exact hzc)
    omega


theorem cycle_power_dyadic_crossed_first_missing (S : ℕ → Bool) (a0 : ℕ) (h : S a0 = false) :
    ∃ L, L ≤ a0 ∧ S L = false ∧ ∀ b < L, S b = true := by
  have hex : ∃ b, S b = false := ⟨a0, h⟩
  refine ⟨Nat.find hex, Nat.find_min' hex h, Nat.find_spec hex, fun b hb => ?_⟩
  simpa using Nat.find_min hex hb

theorem cycle_power_dyadic_crossed_last_missing (S : ℕ → Bool) (N a0 : ℕ) (ha : a0 < N)
    (h : S a0 = false) :
    ∃ c, a0 ≤ c ∧ c < N ∧ S c = false ∧ ∀ b, c < b → b < N → S b = true := by
  refine ⟨Nat.findGreatest (fun b => S b = false) (N - 1), Nat.le_findGreatest (by omega) h,
    by have := Nat.findGreatest_le (P := fun b => S b = false) (N - 1); omega,
    Nat.findGreatest_spec (P := fun b => S b = false) (show a0 ≤ N - 1 by omega) h, ?_⟩
  intro b hb1 hb2
  simpa using Nat.findGreatest_is_greatest hb1 (by omega)

theorem cycle_power_dyadic_crossed_log (R : ℕ) (hR : R ≠ 0) :
    ∃ k, 2 ^ k ≤ R ∧ R < 2 * 2 ^ k := by
  refine ⟨Nat.log 2 R, Nat.pow_log_le_self 2 hR, ?_⟩
  have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) R
  rw [pow_succ] at this; omega

theorem cycle_power_dyadic_crossed_no_island_models_ne_aux (m : ℕ) (hm : 1 ≤ m) (y z : ℤ → ℕ → Bool)
    (ytight : ∀ p, cycle_power_dyadic_class_weight m (y p) =
      (Finset.range (2^m)).sum (fun a => (y p a).toNat))
    (ztight : ∀ p, cycle_power_dyadic_class_weight m (z p) =
      (Finset.range (2^m)).sum (fun a => (z p a).toNat))
    (yexact : ∀ j < m, ∀ v : ℤ, (Finset.range (2^j)).sum (fun a =>
      (y (v-(a : ℤ)) a && y (v-(a : ℤ)) (a+2^m-2^j)).toNat) = 1)
    (zexact : ∀ j < m, ∀ v : ℤ, (Finset.range (2^j)).sum (fun a =>
      (z (v-(a : ℤ)) a && z (v-(a : ℤ)) (a+2^m-2^j)).toNat) = 1)
    (yshape : ∀ (p : ℤ) (a b c : ℕ), a < b → b < c → c < 2^m →
      y p a = false → y p b = true → y p c = true)
    (zshape : ∀ (p : ℤ) (a b c : ℕ), a < b → b < c → c < 2^m →
      z p a = false → z p b = true → z p c = true)
    (hcross : ∀ j : ℕ, 1 ≤ j → j < m → ∀ v : ℤ,
      (∃ a : ℕ, a < 2^j ∧ y (v-(a : ℤ)) a = true ∧ z (v-(a : ℤ)) (a+2^m-2^j) = true) ∧
      (∃ a : ℕ, a < 2^j ∧ z (v-(a : ℤ)) a = true ∧ y (v-(a : ℤ)) (a+2^m-2^j) = true))
    (p : ℤ) (a0 : ℕ) (ha0 : a0 < 2^m) (hya : y p a0 = false) (hza : z p a0 = true) :
    False := by
  have yend : ∀ q : ℤ, y q 0 = true ∧ y q (2^m-1) = true := by
    intro q
    have hh := yexact 0 (by omega) q
    simp only [pow_zero, Finset.sum_range_one, Nat.cast_zero, sub_zero, Nat.zero_add] at hh
    revert hh
    cases y q 0 <;> cases y q (2^m-1) <;> decide
  have ha00 : a0 ≠ 0 := by
    intro h; rw [h, (yend p).1] at hya; exact absurd hya (by decide)
  have ha0N : a0 ≠ 2^m - 1 := by
    intro h; rw [h, (yend p).2] at hya; exact absurd hya (by decide)
  have hm2 : 2 ≤ m := by
    by_contra h
    have h1 : m = 1 := by omega
    subst h1
    norm_num at ha0 ha0N
    omega
  have hN1 : 2 ^ m = 2 * 2 ^ (m - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hN2 : 2 ^ (m - 1) = 2 * 2 ^ (m - 2) := by
    rw [← pow_succ']; congr 1; omega
  have hpos2 : 0 < 2 ^ (m - 2) := Nat.two_pow_pos _
  have PR := cycle_power_dyadic_crossed_prefix_rule m y z ytight ztight yexact zexact yshape
    (fun j h1 h2 v => (hcross j h1 h2 v).1)
  have SR := cycle_power_dyadic_crossed_suffix_rule m y z ytight ztight yexact zexact yshape
    (fun j h1 h2 v => (hcross j h1 h2 v).2)
  have plt : ∀ a b : ℕ, 2 ^ a < 2 ^ b → a < b := fun a b h =>
    (Nat.pow_lt_pow_iff_right (by norm_num)).mp h
  have pmono : ∀ a b : ℕ, a ≤ b → 2 ^ a ≤ 2 ^ b := fun a b h => Nat.pow_le_pow_right (by norm_num) h
  have psucc : ∀ a : ℕ, 2 ^ (a + 1) = 2 * 2 ^ a := fun a => by rw [pow_succ]; ring
  rcases cycle_power_dyadic_crossed_run m (z p) (zshape p) a0 hza with hpre | hsuf
  · -- z holds the whole initial run up to a0
    obtain ⟨L, hLa, hyL, hy⟩ := cycle_power_dyadic_crossed_first_missing (y p) a0 hya
    have hzL : z p L = true := hpre _ hLa
    have hL0 : L ≠ 0 := by
      intro h; rw [h, (yend p).1] at hyL; exact absurd hyL (by decide)
    obtain ⟨k, hk1, hk2⟩ := cycle_power_dyadic_crossed_log L hL0
    have hk2' : L < 2 ^ (k + 1) := by rw [psucc]; exact hk2
    have hkm : k < m := plt _ _ (by omega)
    rcases Nat.lt_or_ge (k + 1) m with hk | hk
    · have hkk := pmono _ _ (show k + 1 ≤ m by omega)
      rw [psucc] at hkk
      by_cases hR : y p (2 ^ m - 2 ^ k) = true
      · exact PR p L k hk hk1 hk2' (fun b hb => hy b (by omega)) hR hyL hzL
      · have hR' : y p (2 ^ m - 2 ^ k) = false := by simpa using hR
        have hLeq : L = 2 ^ k := by
          by_contra hne
          have h2k := hy _ (show 2 ^ k < L by omega)
          have := cycle_power_dyadic_crossed_parent_hi m k hk (y p) (ytight p) _ le_rfl
            (by rw [psucc]; omega) h2k
          rw [show 2 ^ k + 2 ^ m - 2 ^ (k + 1) = 2 ^ m - 2 ^ k by rw [psucc]; omega] at this
          rw [this] at hR'; exact absurd hR' (by decide)
        have hz2k : z p (2 ^ k) = true := hpre _ (by omega)
        have hzN := cycle_power_dyadic_crossed_parent_hi m k hk (z p) (ztight p) _ le_rfl
          (by rw [psucc]; omega) hz2k
        rw [show 2 ^ k + 2 ^ m - 2 ^ (k + 1) = 2 ^ m - 2 ^ k by rw [psucc]; omega] at hzN
        have hzsuf := cycle_power_dyadic_crossed_big_suffix m k (by omega) (z p) (ztight p)
          (zshape p) hzN
        obtain ⟨c, hcge, hclt, hyc, hyabove⟩ :=
          cycle_power_dyadic_crossed_last_missing (y p) (2 ^ m) (2 ^ m - 2 ^ k) (by omega) hR'
        have hcne : c ≠ 2 ^ m - 1 := by
          intro h; rw [h, (yend p).2] at hyc; exact absurd hyc (by decide)
        have hzc := hzsuf _ hcge hclt
        obtain ⟨k', hk'1, hk'2⟩ := cycle_power_dyadic_crossed_log (2 ^ m - 1 - c) (by omega)
        have hk'k : k' ≤ k := by
          by_contra h
          have := pmono _ _ (show k + 1 ≤ k' by omega)
          rw [psucc] at this; omega
        have hpk' := pmono _ _ hk'k
        exact SR p c k' (by omega) (by rw [psucc]; omega) (by omega)
          (fun b hb1 hb2 => hyabove b (by omega) hb2) (hy _ (by omega)) hyc hzc
    · have hkeq : k = m - 1 := by omega
      subst hkeq
      have hy34 : ∀ b, 2 ^ m - 2 ^ (m - 2) ≤ b → b < 2 ^ m → y p b = true := by
        intro b hb1 hb2
        have := cycle_power_dyadic_crossed_parent_hi m (m - 2) (by omega) (y p) (ytight p)
          (b - 2 ^ (m - 1)) (by omega) (by rw [show m - 2 + 1 = m - 1 by omega]; omega)
          (hy _ (by omega))
        rw [show m - 2 + 1 = m - 1 by omega,
          show b - 2 ^ (m - 1) + 2 ^ m - 2 ^ (m - 1) = b by omega] at this
        exact this
      have hL34 : L < 2 ^ m - 2 ^ (m - 2) := by
        by_contra h
        have := hy34 L (by omega) (by omega)
        rw [hyL] at this; exact absurd this (by decide)
      exact SR p L (m - 2) (by omega) (by rw [show m - 2 + 1 = m - 1 by omega]; omega) hL34 hy34
        (hy (2 ^ (m - 2) - 1) (by omega)) hyL hzL
  · -- z holds the whole terminal run from a0
    obtain ⟨c, hca, hclt, hyc, hyabove⟩ :=
      cycle_power_dyadic_crossed_last_missing (y p) (2 ^ m) a0 ha0 hya
    have hcne : c ≠ 2 ^ m - 1 := by
      intro h; rw [h, (yend p).2] at hyc; exact absurd hyc (by decide)
    have hzc := hsuf _ hca hclt
    obtain ⟨k, hk1, hk2⟩ := cycle_power_dyadic_crossed_log (2 ^ m - 1 - c) (by omega)
    have hkm : k < m := plt _ _ (by omega)
    rcases Nat.lt_or_ge (k + 1) m with hk | hk
    · have hkk := pmono _ _ (show k + 1 ≤ m by omega)
      rw [psucc] at hkk
      by_cases hR : y p (2 ^ k - 1) = true
      · exact SR p c k hk (by rw [psucc]; omega) (by omega)
          (fun b hb1 hb2 => hyabove b (by omega) hb2) hR hyc hzc
      · have hR' : y p (2 ^ k - 1) = false := by simpa using hR
        have hk0 : 0 < 2 ^ k := Nat.two_pow_pos _
        have hceq : c = 2 ^ m - 1 - 2 ^ k := by
          by_contra hne
          have h1 := hyabove (2 ^ m - 1 - 2 ^ k) (by omega) (by omega)
          have := cycle_power_dyadic_crossed_parent_lo m k hk (y p) (ytight p) (2 ^ k - 1) (by omega)
            (by rw [show 2 ^ k - 1 + 2 ^ m - 2 ^ (k + 1) = 2 ^ m - 1 - 2 ^ k by rw [psucc]; omega]
                exact h1)
          rw [this] at hR'; exact absurd hR' (by decide)
        have hzc' := hsuf (2 ^ m - 1 - 2 ^ k) (by omega) (by omega)
        have hzP := cycle_power_dyadic_crossed_parent_lo m k hk (z p) (ztight p) (2 ^ k - 1) (by omega)
          (by rw [show 2 ^ k - 1 + 2 ^ m - 2 ^ (k + 1) = 2 ^ m - 1 - 2 ^ k by rw [psucc]; omega]
              exact hzc')
        have hzpre := cycle_power_dyadic_crossed_big_prefix m k (by omega) (z p) (ztight p)
          (zshape p) hzP
        obtain ⟨L, hLle, hyL, hy⟩ := cycle_power_dyadic_crossed_first_missing (y p) _ hR'
        have hL0 : L ≠ 0 := by
          intro h; rw [h, (yend p).1] at hyL; exact absurd hyL (by decide)
        have hzL := hzpre L (by omega)
        obtain ⟨l, hl1, hl2⟩ := cycle_power_dyadic_crossed_log L hL0
        have hlk : l < k := plt _ _ (by omega)
        have hpl := pmono _ _ hlk.le
        exact PR p L l (by omega) hl1 (by rw [psucc]; omega) (fun b hb => hy b (by omega))
          (hyabove _ (by omega) (by omega)) hyL hzL
    · have hkeq : k = m - 1 := by omega
      subst hkeq
      have hy0 : ∀ b < 2 ^ (m - 2), y p b = true := by
        intro b hb
        exact cycle_power_dyadic_crossed_parent_lo m (m - 2) (by omega) (y p) (ytight p) b hb
          (by rw [show m - 2 + 1 = m - 1 by omega]; exact hyabove _ (by omega) (by omega))
      have hc4 : 2 ^ (m - 2) ≤ c := by
        by_contra h
        rw [hy0 _ (by omega)] at hyc; exact absurd hyc (by decide)
      exact PR p c (m - 2) (by omega) hc4 (by rw [show m - 2 + 1 = m - 1 by omega]; omega) hy0
        (hyabove _ (by omega) (by omega)) hyc hzc

theorem cycle_power_dyadic_crossed_no_island_models_eq (m : ℕ) (hm : 1 ≤ m) (y z : ℤ → ℕ → Bool)
    (ytight : ∀ p, cycle_power_dyadic_class_weight m (y p) =
      (Finset.range (2^m)).sum (fun a => (y p a).toNat))
    (ztight : ∀ p, cycle_power_dyadic_class_weight m (z p) =
      (Finset.range (2^m)).sum (fun a => (z p a).toNat))
    (yexact : ∀ j < m, ∀ v : ℤ, (Finset.range (2^j)).sum (fun a =>
      (y (v-(a : ℤ)) a && y (v-(a : ℤ)) (a+2^m-2^j)).toNat) = 1)
    (zexact : ∀ j < m, ∀ v : ℤ, (Finset.range (2^j)).sum (fun a =>
      (z (v-(a : ℤ)) a && z (v-(a : ℤ)) (a+2^m-2^j)).toNat) = 1)
    (yshape : ∀ (p : ℤ) (a b c : ℕ), a < b → b < c → c < 2^m →
      y p a = false → y p b = true → y p c = true)
    (zshape : ∀ (p : ℤ) (a b c : ℕ), a < b → b < c → c < 2^m →
      z p a = false → z p b = true → z p c = true)
    (hcross : ∀ j : ℕ, 1 ≤ j → j < m → ∀ v : ℤ,
      (∃ a : ℕ, a < 2^j ∧ y (v-(a : ℤ)) a = true ∧ z (v-(a : ℤ)) (a+2^m-2^j) = true) ∧
      (∃ a : ℕ, a < 2^j ∧ z (v-(a : ℤ)) a = true ∧ y (v-(a : ℤ)) (a+2^m-2^j) = true)) :
    ∀ (p : ℤ) (a : ℕ), a < 2^m → y p a = z p a := by
  intro p a ha
  cases hy : y p a <;> cases hz : z p a
  · rfl
  · exact (cycle_power_dyadic_crossed_no_island_models_ne_aux m hm y z ytight ztight yexact zexact yshape zshape hcross p a ha hy hz).elim
  · exact (cycle_power_dyadic_crossed_no_island_models_ne_aux m hm z y ztight ytight zexact yexact
      zshape yshape (fun j h1 h2 v => ⟨(hcross j h1 h2 v).2, (hcross j h1 h2 v).1⟩) p a ha hz hy).elim
  · rfl
