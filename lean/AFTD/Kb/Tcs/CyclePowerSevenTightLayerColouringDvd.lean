import AFTD.Prelude

/-!
# cycle_power_seven_tight_layer_colouring_dvd

Topic: graphs   Node: 05c91f7ff62e

Provenance: helper lemma. step for simple_graph_cycle_power_seven_cover_four_tight_dvd (research thread RT-1, open case k = 7 of OP-205, arXiv:2610.15635)

Colouring core of the k = 7 lower bound. Positions of Z/n alternate between N-positions (where N holds) and P-positions, a is 4-periodic on the N-positions, and at every N-position p, with X = σ(p-2) if a(p-2) and σ(p-4) otherwise, the values σ p, σ(p-6), X are distinct and differ from both σ(p+1) and σ(p-7). Then 8 divides n. These are the layers of the four classes through the vertices p+1 and p in a tight 4-cover of C_n^7, once the class types are known.
-/

theorem cycle_power_seven_tight_layer_colouring_dvd (n : ℕ) [NeZero n] (σ : ZMod n → Fin 4)
    (N a : ZMod n → Bool) (hN : ∀ p, N (p + 1) = !N p)
    (ha : ∀ p, N p = true → a p = a (p - 4))
    (hP : ∀ p, N p = true → ∀ X : Fin 4, X = (if a (p - 2) = true then σ (p - 2) else σ (p - 4)) →
      σ p ≠ σ (p - 6) ∧ σ p ≠ X ∧ σ (p - 6) ≠ X ∧
      σ (p + 1) ≠ σ p ∧ σ (p + 1) ≠ σ (p - 6) ∧ σ (p + 1) ≠ X ∧
      σ (p - 7) ≠ σ p ∧ σ (p - 7) ≠ σ (p - 6) ∧ σ (p - 7) ≠ X) :
    8 ∣ n := by
  have hN2 : ∀ p, N (p - 2) = N p := by
    intro p
    have h1 := hN (p - 2); have h2 := hN (p - 2 + 1)
    rw [show p - 2 + 1 + 1 = p by ring, h1] at h2
    rw [h2]; simp
  have hNk : ∀ p, N p = true → N (p - 2) = true ∧ N (p - 4) = true ∧ N (p - 6) = true ∧
      N (p - 8) = true ∧ N (p + 2) = true := by
    intro p hp
    have e2 : N (p - 2) = true := by rw [hN2]; exact hp
    have e4 : N (p - 4) = true := by rw [show p - 4 = p - 2 - 2 by ring, hN2]; exact e2
    have e6 : N (p - 6) = true := by rw [show p - 6 = p - 4 - 2 by ring, hN2]; exact e4
    have e8 : N (p - 8) = true := by rw [show p - 8 = p - 6 - 2 by ring, hN2]; exact e6
    have e2' : N (p + 2) = true := by rw [← hN2, show p + 2 - 2 = p by ring]; exact hp
    exact ⟨e2, e4, e6, e8, e2'⟩
  have pig : ∀ x b c d e : Fin 4, x ≠ b → x ≠ c → x ≠ d → b ≠ c → b ≠ d → c ≠ d →
      e ≠ b → e ≠ c → e ≠ d → e = x := by
    intro x b c d e h1 h2 h3 h4 h5 h6 h7 h8 h9
    simp only [ne_eq, Fin.ext_iff] at *
    omega
  -- the layers repeat at distance 8
  have h8 : ∀ q, σ (q - 8) = σ q := by
    intro q
    by_cases hq : N q = true
    · obtain ⟨hq2, hq4, hq6, hq8, -⟩ := hNk q hq
      have a26 := ha (q - 2) hq2
      have a48 := ha (q - 4) hq4
      rw [show q - 2 - 4 = q - 6 by ring] at a26
      rw [show q - 4 - 4 = q - 8 by ring] at a48
      have F0 := hP q hq _ rfl
      have F2 := hP (q - 2) hq2 _ rfl
      have F4 := hP (q - 4) hq4 _ rfl
      have F6 := hP (q - 6) hq6 _ rfl
      have F8 := (hP (q - 8) hq8 _ rfl).2.2.2.1
      rw [show q - 8 + 1 = q - 7 by ring] at F8
      rw [show q - 2 - 2 = q - 4 by ring, show q - 2 - 6 = q - 8 by ring,
        show q - 2 - 4 = q - 6 by ring] at F2
      rw [show q - 4 - 2 = q - 6 by ring, show q - 4 - 4 = q - 8 by ring, ← a26] at F4
      rw [show q - 6 - 2 = q - 8 by ring, ← a48] at F6
      revert F0 F2 F4 F6
      cases h2 : a (q - 2) <;> cases h4 : a (q - 4) <;>
        simp only [if_true, if_false, Bool.false_eq_true] <;>
        intro F0 F2 F4 F6 <;>
        obtain ⟨-, -, -, -, -, -, g1, g2, g3⟩ := id F0
      · exact pig _ _ _ _ _ F0.1 F0.2.1 (Ne.symm g1) F0.2.2.1 (Ne.symm g2) (Ne.symm g3)
          F2.2.2.1 (Ne.symm F4.2.1) (Ne.symm F8)
      · exact pig _ _ _ _ _ F0.1 F0.2.1 (Ne.symm g1) F0.2.2.1 (Ne.symm g2) (Ne.symm g3)
          (Ne.symm F6.2.1) (Ne.symm F4.2.1) (Ne.symm F8)
      · exact pig _ _ _ _ _ F0.1 F0.2.1 (Ne.symm g1) F0.2.2.1 (Ne.symm g2) (Ne.symm g3)
          F2.2.2.1 (Ne.symm F2.1) (Ne.symm F8)
      · exact pig _ _ _ _ _ F0.1 F0.2.1 (Ne.symm g1) F0.2.2.1 (Ne.symm g2) (Ne.symm g3)
          (Ne.symm F6.2.1) (Ne.symm F2.1) (Ne.symm F8)
    · have hp : N (q - 1) = true := by
        have := hN (q - 1); rw [sub_add_cancel] at this; rw [this] at hq; simpa using hq
      obtain ⟨f1, f2, f3, f4, f5, f6, f7, f8, f9⟩ := hP (q - 1) hp _ rfl
      rw [sub_add_cancel] at f4 f5 f6
      rw [show q - 1 - 7 = q - 8 by ring] at f7 f8 f9
      exact pig _ _ _ _ _ f4 f5 f6 f1 f2 f3 f7 f8 f9
  -- somewhere the layers do not repeat at distance 4
  have hex : ∃ q, σ (q - 4) ≠ σ q := by
    obtain ⟨p, hp⟩ : ∃ p, N p = true := by
      by_cases h0 : N 0 = true
      · exact ⟨0, h0⟩
      · refine ⟨1, ?_⟩; have := hN 0; rw [zero_add] at this; rw [this]; simpa using h0
    obtain ⟨-, -, -, -, hp2⟩ := hNk p hp
    have F0 := hP p hp _ rfl
    have F2 := hP (p + 2) hp2 _ rfl
    rw [show p + 2 - 2 = p by ring, show p + 2 - 6 = p - 4 by ring] at F2
    revert F0 F2
    cases h2 : a (p - 2) <;> cases h0 : a p <;>
      simp only [if_true, if_false, Bool.false_eq_true] <;> intro F0 F2
    · exact ⟨p, fun h => F0.2.1 h.symm⟩
    · exact ⟨p, fun h => F0.2.1 h.symm⟩
    · exact ⟨p + 2, fun h => F2.2.1 h.symm⟩
    · exact ⟨p, F2.2.2.1⟩
  have hZ : ∀ z : ℤ, ∀ q, σ (q + 8 * (z : ZMod n)) = σ q := by
    intro z
    induction z using Int.induction_on with
    | zero => intro q; simp
    | succ k ih =>
      intro q
      have := h8 (q + 8 * (((k : ℤ) + 1 : ℤ) : ZMod n))
      rw [← this, ← ih q]; congr 1; push_cast; ring
    | pred k ih =>
      intro q
      have := h8 (q + 8 * ((-(k : ℤ) : ℤ) : ZMod n))
      rw [ih q] at this; rw [← this]; congr 1; push_cast; ring
  by_contra hnd
  obtain ⟨g, hg⟩ : ∃ g, g = Nat.gcd 8 n := ⟨_, rfl⟩
  have hg8 : g ∣ 8 := hg ▸ Nat.gcd_dvd_left 8 n
  have hgn : g ∣ n := hg ▸ Nat.gcd_dvd_right 8 n
  have hg4 : g ∣ 4 := by
    have hgle : g ≤ 8 := Nat.le_of_dvd (by norm_num) hg8
    have hne : g ≠ 8 := fun h => hnd (h ▸ hgn)
    interval_cases g <;> first | decide | (exfalso; revert hg8; decide) | exact absurd rfl hne
  obtain ⟨w, hw⟩ := hg4
  have hb : ((Nat.gcd 8 n : ℕ) : ℤ) = 8 * Nat.gcdA 8 n + n * Nat.gcdB 8 n := Nat.gcd_eq_gcd_ab 8 n
  have h4z : ((4 : ℤ) : ZMod n) = ((8 * (Nat.gcdA 8 n * w) + n * (Nat.gcdB 8 n * w) : ℤ) : ZMod n) := by
    congr 1
    have : (4 : ℤ) = ((g * w : ℕ) : ℤ) := by rw [← hw]; rfl
    rw [this, hg]; push_cast; rw [hb]; ring
  push_cast at h4z
  rw [ZMod.natCast_self, zero_mul, add_zero] at h4z
  obtain ⟨q, hq⟩ := hex
  apply hq
  rw [← hZ (-(Nat.gcdA 8 n * w)) q]
  congr 1; push_cast; linear_combination (-1 : ZMod n) * h4z
