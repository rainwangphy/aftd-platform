import AFTD.Prelude

/-!
# cycle_power_dyadic_type_layer_periods_dvd

Topic: combinatorics   Node: b6157ee093b3

Provenance: helper lemma. Uniform helper for the OP-205 / RT-1 campaign, following arXiv:2610.15635, Section 3. These conditional class-system and pruning lemmas do not establish the unresolved graph covering bound. The earlier fixed-radius helpers handle radii eight and sixteen; this session works with arbitrary dyadic radii. No research advance is claimed.

For cyclic classes of arc length 2^(m+1), type period 2^m and label period 2^(m+1) force 2^(m+1) to divide the cycle length, if distinct overlapping classes have different labels and some class contains a distance-2^m pair. Labels can lie in any type.
-/

open Finset

theorem cycle_power_dyadic_type_layer_periods_dvd
    (m n : ℕ) [NeZero n] {α : Type*}
    (σ : ZMod n → α) (x : ZMod n → ℕ → Bool)
    (htype : ∀ p j, x (p + ((2 ^ m : ℕ) : ZMod n)) j = x p j)
    (hlayer : ∀ p, σ (p + ((2 ^ (m + 1) : ℕ) : ZMod n)) = σ p)
    (hsep : ∀ (p q : ZMod n) (j k : ℕ), j < 2 ^ (m + 1) → k < 2 ^ (m + 1) →
      p + (j : ZMod n) = q + (k : ZMod n) →
      x p j = true → x q k = true → σ p = σ q → j = k)
    (hpair : ∃ (p : ZMod n) (a : ℕ), a < 2 ^ m ∧
      x p a = true ∧ x p (a + 2 ^ m) = true) :
    2 ^ (m + 1) ∣ n := by
  let D := 2 ^ (m + 1)
  let H := 2 ^ m
  have hD : D = 2 * H := by dsimp [D, H]; rw [pow_succ]; omega
  have hHpos : 0 < H := Nat.two_pow_pos _
  have hback : ∀ p, σ (p - (D : ZMod n)) = σ p := by
    intro p
    have h := hlayer (p - (D : ZMod n))
    rw [sub_add_cancel] at h
    exact h.symm
  have hZ : ∀ z : ℤ, ∀ q, σ (q + (D : ZMod n) * (z : ZMod n)) = σ q := by
    intro z
    induction z using Int.induction_on with
    | zero => intro q; simp
    | succ k ih =>
      intro q
      have h := hback (q + (D : ZMod n) * (((k : ℤ) + 1 : ℤ) : ZMod n))
      rw [← h, ← ih q]
      congr 1
      push_cast
      ring
    | pred k ih =>
      intro q
      have h := hback (q + (D : ZMod n) * ((-(k : ℤ) : ℤ) : ZMod n))
      rw [ih q] at h
      rw [← h]
      congr 1
      push_cast
      ring
  by_contra hnd
  let g := Nat.gcd D n
  have hgD : g ∣ D := Nat.gcd_dvd_left D n
  have hgn : g ∣ n := Nat.gcd_dvd_right D n
  have hgH : g ∣ H := by
    obtain ⟨k, hk, hg⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hgD
    have hk' : k ≤ m := by
      by_contra hn
      have hke : k = m + 1 := by omega
      have hge : g = D := by simpa only [hke] using hg
      apply hnd
      change D ∣ n
      rw [← hge]
      exact hgn
    rw [hg]
    exact ⟨2 ^ (m - k), by dsimp [H]; rw [← pow_add]; congr 1; omega⟩
  obtain ⟨w, hw⟩ := hgH
  have hb : ((Nat.gcd D n : ℕ) : ℤ) =
      D * Nat.gcdA D n + n * Nat.gcdB D n := Nat.gcd_eq_gcd_ab D n
  have hHzInt : (H : ℤ) =
      (D : ℤ) * (Nat.gcdA D n * w) + n * (Nat.gcdB D n * w) := by
    calc (H : ℤ) = (g : ℤ) * (w : ℤ) := by exact_mod_cast hw
         _ = _ := by dsimp [g]; rw [hb]; ring
  have hHz := congrArg (fun z : ℤ => (z : ZMod n)) hHzInt
  push_cast at hHz
  rw [ZMod.natCast_self, zero_mul, add_zero] at hHz
  have hhalf : ∀ p, σ (p + (H : ZMod n)) = σ p := by
    intro p
    rw [hHz]
    simpa only [Int.cast_mul, Int.cast_natCast] using hZ (Nat.gcdA D n * w) p
  obtain ⟨p, a, ha, hxa, hxah⟩ := hpair
  have hxa' : x (p + (H : ZMod n)) a = true := by
    rw [htype]
    exact hxa
  have h := hsep p (p + (H : ZMod n)) (a + H) a (by dsimp [H] at *; omega) (by omega)
    (by push_cast; ring) hxah hxa' (hhalf p).symm
  omega
