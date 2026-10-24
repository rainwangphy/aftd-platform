import AFTD.Prelude

/-!
# cycle_power_fifteen_type_layer_periods_dvd

Topic: combinatorics   Node: 1496169a4678

Provenance: helper lemma. Period reduction for the k = 15 case of RT-1 and OP-205, arXiv:2610.15635; the Bezout argument adapts cycle_power_seven_tight_layer_colouring_dvd. Experiment 3987 motivates the two periods.

For sixteen-position classes on a cyclic index set, type period 8 and layer-label period 16 force 16 to divide the cycle length, provided distinct overlapping classes have different labels and some class contains a distance-8 pair. Labels may lie in any type.
-/

theorem cycle_power_fifteen_type_layer_periods_dvd (n : ℕ) [NeZero n] {α : Type*}
    (σ : ZMod n → α) (x : ZMod n → Fin 16 → Bool)
    (htype : ∀ p j, x (p + 8) j = x p j)
    (hlayer : ∀ p, σ (p + 16) = σ p)
    (hsep : ∀ (p q : ZMod n) (j k : Fin 16),
      p + ((j : ℕ) : ZMod n) = q + ((k : ℕ) : ZMod n) →
      x p j = true → x q k = true → σ p = σ q → j = k)
    (hpair : ∃ (p : ZMod n) (a : Fin 8),
      x p ⟨a.val, by omega⟩ = true ∧ x p ⟨a.val + 8, by omega⟩ = true) :
    16 ∣ n := by
  have h16 : ∀ p, σ (p - 16) = σ p := by
    intro p
    have h := hlayer (p - 16)
    rw [sub_add_cancel] at h
    exact h.symm
  have hZ : ∀ z : ℤ, ∀ q, σ (q + 16 * (z : ZMod n)) = σ q := by
    intro z
    induction z using Int.induction_on with
    | zero => intro q; simp
    | succ k ih =>
      intro q
      have h := h16 (q + 16 * (((k : ℤ) + 1 : ℤ) : ZMod n))
      rw [← h, ← ih q]
      congr 1
      push_cast
      ring
    | pred k ih =>
      intro q
      have h := h16 (q + 16 * ((-(k : ℤ) : ℤ) : ZMod n))
      rw [ih q] at h
      rw [← h]
      congr 1
      push_cast
      ring
  by_contra hnd
  obtain ⟨g, hg⟩ : ∃ g, g = Nat.gcd 16 n := ⟨_, rfl⟩
  have hg16 : g ∣ 16 := hg ▸ Nat.gcd_dvd_left 16 n
  have hgn : g ∣ n := hg ▸ Nat.gcd_dvd_right 16 n
  have hg8 : g ∣ 8 := by
    have hgle : g ≤ 16 := Nat.le_of_dvd (by norm_num) hg16
    have hne : g ≠ 16 := fun h => hnd (h ▸ hgn)
    interval_cases g <;> first | decide | (exfalso; revert hg16; decide) | exact absurd rfl hne
  obtain ⟨w, hw⟩ := hg8
  have hb : ((Nat.gcd 16 n : ℕ) : ℤ) =
      16 * Nat.gcdA 16 n + n * Nat.gcdB 16 n := Nat.gcd_eq_gcd_ab 16 n
  have h8z : ((8 : ℤ) : ZMod n) =
      ((16 * (Nat.gcdA 16 n * w) + n * (Nat.gcdB 16 n * w) : ℤ) : ZMod n) := by
    congr 1
    have h : (8 : ℤ) = ((g * w : ℕ) : ℤ) := by rw [← hw]; rfl
    rw [h, hg]
    push_cast
    rw [hb]
    ring
  push_cast at h8z
  rw [ZMod.natCast_self, zero_mul, add_zero] at h8z
  have h8 : ∀ p, σ (p + 8) = σ p := by
    intro p
    rw [h8z]
    simpa only [Int.cast_mul, Int.cast_natCast] using hZ (Nat.gcdA 16 n * w) p
  obtain ⟨p, a, ha, ha8⟩ := hpair
  have ha' : x (p + 8) ⟨a.val, by omega⟩ = true := by
    rw [htype]
    exact ha
  have h := hsep p (p + 8) ⟨a.val + 8, by omega⟩ ⟨a.val, by omega⟩
    (by push_cast; ring) ha8 ha' (h8 p).symm
  have hval := congrArg Fin.val h
  dsimp at hval
  omega
