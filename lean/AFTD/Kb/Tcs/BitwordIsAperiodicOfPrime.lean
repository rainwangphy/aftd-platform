import AFTD.Prelude
import AFTD.Kb.Tcs.BitwordIsAperiodic
import AFTD.Kb.Tcs.BitwordRotate

/-!
# bitword_is_aperiodic_of_prime

Topic: combinatorics   Node: 8712fdf733bc

Provenance: helper lemma. for brgc_necklace_order_consecutive_aperiodic_adjacent: it gives the prime case of arXiv:2610.24758 Conjecture 1

For prime n, every n-bit word other than 0^n and 1^n is aperiodic.
-/

lemma bitword_is_aperiodic_of_prime_rotate_eq_self {n x : ℕ} (hn : 1 ≤ n) (hx : x < 2 ^ n)
    (h : bitword_rotate n x = x) : x = 0 ∨ x = 2 ^ n - 1 := by
  dsimp [bitword_rotate] at h
  set K := 2 ^ (n - 1)
  have hK : 0 < K := by positivity
  have hM : 2 ^ n = 2 * K := by
    have : n = n - 1 + 1 := (Nat.sub_add_cancel hn).symm
    nth_rw 1 [this]
    rw [pow_succ', mul_comm]
  rcases lt_or_ge x K with hlt | hge
  · have hdiv : x / K = 0 := Nat.div_eq_of_lt hlt
    have h2x : 2 * x < 2 ^ n := by omega
    have hmod : 2 * x % 2 ^ n = 2 * x := Nat.mod_eq_of_lt h2x
    omega
  · have hdiv : x / K = 1 := by
      apply Nat.div_eq_of_lt_le
      · omega
      · rw [add_one_mul, one_mul]; omega
    have h2x_ge : 1 * 2 ^ n ≤ 2 * x := by omega
    have h2x_lt : 2 * x < (1 + 1) * 2 ^ n := by omega
    have hd : 2 * x / 2 ^ n = 1 := Nat.div_eq_of_lt_le h2x_ge h2x_lt
    have hmod : 2 * x % 2 ^ n = 2 * x - 2 ^ n := by
      have hdm := Nat.div_add_mod (2 * x) (2 ^ n)
      rw [hd] at hdm
      omega
    omega

lemma bitword_is_aperiodic_of_prime_rotate_eq_mod (n x : ℕ) (hn : 2 ≤ n) (hx0 : 0 < x) (hx1 : x < 2 ^ n - 1) :
    bitword_rotate n x = (2 * x) % (2 ^ n - 1) ∧
    0 < bitword_rotate n x ∧ bitword_rotate n x < 2 ^ n - 1 := by
  dsimp [bitword_rotate]
  set K := 2 ^ (n - 1)
  have hK_ge : 2 ≤ K := by
    have : 1 ≤ n - 1 := by omega
    calc 2 = 2 ^ 1 := by norm_num
    _ ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) this
  have hM : 2 ^ n = 2 * K := by
    have : n = n - 1 + 1 := (Nat.sub_add_cancel (by omega : 1 ≤ n)).symm
    nth_rw 1 [this]
    rw [pow_succ', mul_comm]
  rcases lt_or_ge x K with hlt | hge
  · have hdiv : x / K = 0 := Nat.div_eq_of_lt hlt
    have h2x : 2 * x < 2 ^ n := by omega
    have hmod1 : 2 * x % 2 ^ n = 2 * x := Nat.mod_eq_of_lt h2x
    have h2x' : 2 * x < 2 ^ n - 1 := by omega
    have hmod2 : (2 * x) % (2 ^ n - 1) = 2 * x := Nat.mod_eq_of_lt h2x'
    omega
  · have hdiv : x / K = 1 := by
      apply Nat.div_eq_of_lt_le
      · omega
      · rw [add_one_mul, one_mul]; omega
    have hd1 : 2 * x / 2 ^ n = 1 := by
      apply Nat.div_eq_of_lt_le
      · omega
      · rw [add_one_mul, one_mul]; omega
    have hmod1 : 2 * x % 2 ^ n = 2 * x - 2 ^ n := by
      have := Nat.div_add_mod (2 * x) (2 ^ n)
      rw [hd1] at this
      omega
    have hd2 : (2 * x) / (2 ^ n - 1) = 1 := by
      apply Nat.div_eq_of_lt_le
      · omega
      · rw [add_one_mul, one_mul]; omega
    have hmod2 : (2 * x) % (2 ^ n - 1) = 2 * x - 2 ^ n + 1 := by
      have := Nat.div_add_mod (2 * x) (2 ^ n - 1)
      rw [hd2] at this
      omega
    omega

lemma bitword_is_aperiodic_of_prime_iterate_eq_mod (n : ℕ) (hn : 2 ≤ n) (x : ℕ) (hx0 : 0 < x) (hx1 : x < 2 ^ n - 1) (m : ℕ) :
    (bitword_rotate n)^[m] x = (2 ^ m * x) % (2 ^ n - 1) ∧
    0 < (bitword_rotate n)^[m] x ∧ (bitword_rotate n)^[m] x < 2 ^ n - 1 := by
  induction m with
  | zero =>
    simp only [Function.iterate_zero, id_eq, pow_zero, one_mul]
    rw [Nat.mod_eq_of_lt hx1]
    exact ⟨rfl, hx0, hx1⟩
  | succ m ih =>
    rw [Function.iterate_succ', Function.comp_apply]
    obtain ⟨ih_eq, ih_pos, ih_lt⟩ := ih
    have hstep := bitword_is_aperiodic_of_prime_rotate_eq_mod n ((bitword_rotate n)^[m] x) hn ih_pos ih_lt
    refine ⟨?_, hstep.2.1, hstep.2.2⟩
    rw [hstep.1, ih_eq]
    rw [Nat.mul_mod_mod, ← mul_assoc, pow_succ, mul_comm 2 (2 ^ m)]

lemma bitword_is_aperiodic_of_prime_pow_mul_add_one_mul_mod (n q x : ℕ) (hn : 2 ≤ n) :
    (2 ^ (q * n + 1) * x) % (2 ^ n - 1) = (2 * x) % (2 ^ n - 1) := by
  have hM : 1 < 2 ^ n - 1 := by
    have : 4 ≤ 2 ^ n := by
      calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  have h_mod : (2 ^ n) % (2 ^ n - 1) = 1 := by
    have : 2 ^ n = (2 ^ n - 1) + 1 := by omega
    nth_rw 1 [this]
    rw [Nat.add_mod_left, Nat.mod_eq_of_lt (by omega)]
  have h_pow_mod : ((2 ^ n) ^ q) % (2 ^ n - 1) = 1 := by
    rw [Nat.pow_mod, h_mod, one_pow, Nat.mod_eq_of_lt hM]
  have h2k : 2 ^ (q * n + 1) = ((2 ^ n) ^ q) * 2 := by
    rw [pow_add, pow_one, mul_comm q n, pow_mul, mul_comm]
  rw [h2k, mul_assoc, Nat.mul_mod, h_pow_mod, one_mul, Nat.mod_mod]

lemma bitword_is_aperiodic_of_prime_iterate_mul_apply {α : Type*} (f : α → α) (x : α) (r : ℕ) (h : f^[r] x = x) (m : ℕ) :
    f^[m * r] x = x := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [add_one_mul, Function.iterate_add, Function.comp_apply, h, ih]

theorem bitword_is_aperiodic_of_prime (n x : ℕ) (hn : n.Prime) (hx : x < 2 ^ n) (h0 : x ≠ 0)
    (h1 : x ≠ 2 ^ n - 1) : bitword_is_aperiodic n x := by
  intro r hr0 hrn hfix
  have hn2 : 2 ≤ n := hn.two_le
  have hx_pos : 0 < x := by omega
  have hx_lt : x < 2 ^ n - 1 := by omega
  have hcop : r.Coprime n := by
    have hdvd : ¬ n ∣ r := Nat.not_dvd_of_pos_of_lt hr0 hrn
    exact (hn.coprime_iff_not_dvd.mpr hdvd).symm
  obtain ⟨m, hm_lt, hm_mod⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hn2
  have h_div_mod : m * r = (r * m / n) * n + 1 := by
    have hdiv := (Nat.div_add_mod (r * m) n).symm
    rw [hm_mod, mul_comm n] at hdiv
    rw [mul_comm m r]
    exact hdiv
  set q := r * m / n
  have hfix_k : (bitword_rotate n)^[m * r] x = x :=
    bitword_is_aperiodic_of_prime_iterate_mul_apply (bitword_rotate n) x r hfix m
  have h_mod_k := (bitword_is_aperiodic_of_prime_iterate_eq_mod n hn2 x hx_pos hx_lt (m * r)).1
  rw [h_div_mod] at h_mod_k hfix_k
  rw [bitword_is_aperiodic_of_prime_pow_mul_add_one_mul_mod n q x hn2] at h_mod_k
  have h_rot1 := (bitword_is_aperiodic_of_prime_rotate_eq_mod n x hn2 hx_pos hx_lt).1
  rw [← h_rot1] at h_mod_k
  rw [h_mod_k] at hfix_k
  have h_or := bitword_is_aperiodic_of_prime_rotate_eq_self (by omega) hx hfix_k
  rcases h_or with hx0 | hx1'
  · exact h0 hx0
  · exact h1 hx1'
