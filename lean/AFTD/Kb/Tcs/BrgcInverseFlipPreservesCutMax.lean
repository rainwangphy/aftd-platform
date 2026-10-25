import AFTD.Prelude
import AFTD.Kb.Tcs.BrgcInverse
import AFTD.Kb.Tcs.BrgcInverseConcat
import AFTD.Kb.Tcs.BrgcInverseLtTwoPow
import AFTD.Kb.Tcs.BrgcInversePrefix
import AFTD.Kb.Tcs.BrgcWord
import AFTD.Kb.Tcs.BrgcWordInverse

/-!
# brgc_inverse_flip_preserves_cut_max

Topic: combinatorics   Node: 5d5dcf50cade

Provenance: formalization of a published result. Source: Gray-ordered Binary Necklaces (2007), Theorem 3.6, in the equivalent convention of maximal forward Gray rank; the rotation form adds nonconstant-word hypotheses.

If an n-bit word has strictly greater inverse Gray rank than every nontrivial cyclic cut, toggling its last bit has at least as great an inverse Gray rank as every nontrivial cyclic cut of the toggled word.
-/

theorem brgc_aux_inverse_concat_lt_iff {m k a b c : ℕ}
    (ha : a < 2 ^ m) (hb : b < 2 ^ k) (hc : c < 2 ^ k) :
    brgc_inverse (m + k) (2 ^ k * a + b) < brgc_inverse (m + k) (2 ^ k * a + c) ↔
      if brgc_inverse m a % 2 = 0 then brgc_inverse k b < brgc_inverse k c
      else brgc_inverse k c < brgc_inverse k b := by
  rw [brgc_inverse_concat ha hb, brgc_inverse_concat ha hc]
  have hb' := brgc_inverse_lt_two_pow hb
  have hc' := brgc_inverse_lt_two_pow hc
  split_ifs <;> omega

@[simp] theorem brgc_aux_inverse_zero (n : ℕ) : brgc_inverse n 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [brgc_inverse, ih]

theorem brgc_aux_inverse_one {n : ℕ} (hn : 0 < n) : brgc_inverse n 1 = 1 := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  simp [brgc_inverse]

theorem brgc_aux_inverse_flip {n : ℕ} (hn : 0 < n) (x : ℕ) :
    brgc_inverse n (x ^^^ 1) = brgc_inverse n x ^^^ 1 := by
  rw [brgc_aux_inverse_xor, brgc_aux_inverse_one hn]

theorem brgc_aux_concat_flip {k a b : ℕ} (hk : 0 < k) (hb : b < 2 ^ k) :
    (2 ^ k * a + b) ^^^ 1 = 2 ^ k * a + (b ^^^ 1) := by
  have h1 : 1 < 2 ^ k := Nat.one_lt_two_pow (by omega)
  rw [← brgc_aux_xor_high_low a b k hb, Nat.xor_assoc,
    brgc_aux_xor_high_low a (b ^^^ 1) k (Nat.xor_lt_two_pow hb h1)]

theorem brgc_aux_inverse_concat_mod_two {m k a b : ℕ} (ha : a < 2 ^ m) (hb : b < 2 ^ k) :
    brgc_inverse (m + k) (2 ^ k * a + b) % 2 =
      (brgc_inverse m a % 2) ^^^ (brgc_inverse k b % 2) := by
  have hb' : b < 2 ^ (m + k) :=
    lt_of_lt_of_le hb (Nat.pow_le_pow_right (by decide) (by omega))
  rw [← brgc_aux_xor_high_low a b k hb, brgc_aux_inverse_xor]
  rw [show (brgc_inverse (m + k) (2 ^ k * a) ^^^ brgc_inverse (m + k) b) % 2 =
      brgc_inverse (m + k) (2 ^ k * a) % 2 ^^^ brgc_inverse (m + k) b % 2 from
        Nat.xor_mod_two_pow (n := 1)]
  rw [(brgc_aux_inverse_shift m k a ha).2, brgc_aux_inverse_stable hb' hb]

theorem brgc_aux_inverse_concat_parity_swap {m k a b : ℕ}
    (ha : a < 2 ^ m) (hb : b < 2 ^ k) :
    brgc_inverse (m + k) (2 ^ k * a + b) % 2 =
      brgc_inverse (k + m) (2 ^ m * b + a) % 2 := by
  rw [brgc_aux_inverse_concat_mod_two ha hb, brgc_aux_inverse_concat_mod_two hb ha]
  exact Nat.xor_comm _ _

theorem brgc_aux_xor_one_bounds (q : ℕ) :
    q ≤ (q ^^^ 1) + 1 ∧ (q ^^^ 1) ≤ q + 1 ∧ (q ^^^ 1) % 2 ≠ q % 2 := by
  rcases Nat.mod_two_eq_zero_or_one q with hq | hq
  · rw [Nat.xor_one_of_even (Nat.even_iff.mpr hq)]
    omega
  · have ho : Odd q := Nat.odd_iff.mpr hq
    rw [Nat.xor_one_of_odd ho]
    omega

theorem brgc_aux_lt_of_flip_lt_of_parity (q r : ℕ) (h : q ^^^ 1 < r)
    (hp : r % 2 = (q ^^^ 1) % 2) : q < r := by
  obtain ⟨h1, h2, h3⟩ := brgc_aux_xor_one_bounds q
  omega

theorem brgc_aux_prefix_rank {m k a b : ℕ} (ha : a < 2 ^ m) (hb : b < 2 ^ k) :
    brgc_inverse (m + k) (2 ^ k * a + b) / 2 ^ k = brgc_inverse m a := by
  have hh := brgc_inverse_prefix (show k ≤ m + k by omega) (brgc_aux_concat_bound ha hb)
  have hdiv : (2 ^ k * a + b) / 2 ^ k = a := by
    rw [Nat.mul_add_div (Nat.two_pow_pos _), Nat.div_eq_of_lt hb]
    omega
  simpa [hdiv] using hh

theorem brgc_aux_word_prefix_bound {m k x : ℕ} (hx : x < 2 ^ (m + k)) :
    x / 2 ^ k < 2 ^ m := by
  apply (Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _)).mpr
  rwa [← pow_add]

theorem brgc_aux_inverse_inj {n x y : ℕ} (hx : x < 2 ^ n) (hy : y < 2 ^ n)
    (h : brgc_inverse n x = brgc_inverse n y) : x = y := by
  have hh := congrArg brgc_word h
  rwa [brgc_word_inverse hx, brgc_word_inverse hy] at hh

theorem brgc_inverse_flip_preserves_cut_max (n x : ℕ) (hx : x < 2 ^ n)
    (hstrict : ∀ a b u v : ℕ, 0 < a → 0 < b → a + b = n →
      u < 2 ^ a → v < 2 ^ b → x = 2 ^ b * u + v →
      brgc_inverse n (2 ^ a * v + u) < brgc_inverse n x) :
    ∀ a b u v : ℕ, 0 < a → 0 < b → a + b = n →
      u < 2 ^ a → v < 2 ^ b → x ^^^ 1 = 2 ^ b * u + v →
      brgc_inverse n (2 ^ a * v + u) ≤ brgc_inverse n (x ^^^ 1) := by
  intro a b u v ha hb hab hu hv hsplit
  have hn : 0 < n := by omega
  have hvf : v ^^^ 1 < 2 ^ b :=
    Nat.xor_lt_two_pow hv (Nat.one_lt_two_pow (by omega))
  have hxsplit : x = 2 ^ b * u + (v ^^^ 1) := by
    have hh := congrArg (fun z : ℕ => z ^^^ 1) hsplit
    simpa [brgc_aux_concat_flip hb hv] using hh
  by_contra hnot
  have hbad : brgc_inverse n (x ^^^ 1) < brgc_inverse n (2 ^ a * v + u) := by omega
  have hlow := hstrict a b u (v ^^^ 1) ha hb hab hu hvf hxsplit
  have hpar : brgc_inverse n (2 ^ a * v + u) % 2 =
      (brgc_inverse n x ^^^ 1) % 2 := by
    calc
      _ = brgc_inverse n (2 ^ b * u + v) % 2 := by
        simpa only [hab, show b + a = n by omega] using (brgc_aux_inverse_concat_parity_swap hu hv).symm
      _ = brgc_inverse n (x ^^^ 1) % 2 := by rw [hsplit]
      _ = _ := by rw [brgc_aux_inverse_flip hn]
  have hhigh : brgc_inverse n x < brgc_inverse n (2 ^ a * v + u) :=
    brgc_aux_lt_of_flip_lt_of_parity _ _ (by simpa [brgc_aux_inverse_flip hn] using hbad) hpar
  have hqlo : brgc_inverse b (v ^^^ 1) ≤ brgc_inverse n x / 2 ^ a := by
    have hh := Nat.div_le_div_right (Nat.le_of_lt hlow) (c := 2 ^ a)
    have he := brgc_aux_prefix_rank hvf hu
    have hba : b + a = n := by omega
    rw [hba] at he
    rwa [he] at hh
  have hqhi : brgc_inverse n x / 2 ^ a ≤ brgc_inverse b v := by
    have hh := Nat.div_le_div_right (Nat.le_of_lt hhigh) (c := 2 ^ a)
    have he := brgc_aux_prefix_rank hv hu
    have hba : b + a = n := by omega
    rw [hba] at he
    rwa [he] at hh
  rw [brgc_aux_inverse_flip hb] at hqlo
  have hvodd : brgc_inverse b v % 2 = 1 := by
    rcases Nat.mod_two_eq_zero_or_one (brgc_inverse b v) with heven | hodd
    · rw [Nat.xor_one_of_even (Nat.even_iff.mpr heven)] at hqlo
      omega
    · exact hodd
  have hvfpar : brgc_inverse b (v ^^^ 1) % 2 = 0 := by
    rw [brgc_aux_inverse_flip hb, Nat.xor_one_of_odd (Nat.odd_iff.mpr hvodd)]
    omega
  have hqc : brgc_inverse n x / 2 ^ a = brgc_inverse b (v ^^^ 1) ∨
      brgc_inverse n x / 2 ^ a = brgc_inverse b v := by
    rw [brgc_aux_inverse_flip hb]
    obtain ⟨h1, h2, _⟩ := brgc_aux_xor_one_bounds (brgc_inverse b v)
    omega
  let e := x / 2 ^ a
  let z := x % 2 ^ a
  have he : e < 2 ^ b := by
    apply brgc_aux_word_prefix_bound
    simpa [Nat.add_comm b a, hab] using hx
  have hz : z < 2 ^ a := Nat.mod_lt _ (Nat.two_pow_pos _)
  have hxez : x = 2 ^ a * e + z := (Nat.div_add_mod x (2 ^ a)).symm
  have hqe : brgc_inverse n x / 2 ^ a = brgc_inverse b e := by
    rw [hxez]
    simpa only [show b + a = n by omega] using brgc_aux_prefix_rank he hz
  have hue : brgc_inverse a u < brgc_inverse a z := by
    rcases hqc with hc | hc
    · have heq : e = v ^^^ 1 := brgc_aux_inverse_inj he hvf (hqe.symm.trans hc)
      have hh : brgc_inverse (b + a) (2 ^ a * (v ^^^ 1) + u) <
          brgc_inverse (b + a) (2 ^ a * (v ^^^ 1) + z) := by
        simpa [show b + a = n by omega, hxez, heq] using hlow
      have hh' := (brgc_aux_inverse_concat_lt_iff hvf hu hz).mp hh
      simpa [hvfpar] using hh'
    · have heq : e = v := brgc_aux_inverse_inj he hv (hqe.symm.trans hc)
      have hh : brgc_inverse (b + a) (2 ^ a * v + z) <
          brgc_inverse (b + a) (2 ^ a * v + u) := by
        simpa [show b + a = n by omega, hxez, heq] using hhigh
      have hh' := (brgc_aux_inverse_concat_lt_iff hv hz hu).mp hh
      simpa [hvodd] using hh'
  have hnew := hstrict b a e z hb ha (by omega) he hz hxez
  have hdiv := Nat.div_le_div_right (Nat.le_of_lt hnew) (c := 2 ^ b)
  have he1 : brgc_inverse n (2 ^ b * z + e) / 2 ^ b = brgc_inverse a z := by
    simpa only [hab] using brgc_aux_prefix_rank hz he
  have he2 : brgc_inverse n x / 2 ^ b = brgc_inverse a u := by
    rw [hxsplit]
    simpa only [hab] using brgc_aux_prefix_rank hu hvf
  rw [he1, he2] at hdiv
  omega
