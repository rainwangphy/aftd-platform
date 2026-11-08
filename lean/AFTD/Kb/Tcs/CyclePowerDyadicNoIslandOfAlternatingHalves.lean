import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.CyclePowerDyadicAlternatingHalfCrossedCover
import AFTD.Kb.Tcs.CyclePowerDyadicCrossedNoIslandModelsEq
import AFTD.Kb.Tcs.CyclePowerDyadicAlternatingHalfModel

/-!
# cycle_power_dyadic_no_island_of_alternating_halves

Topic: combinatorics   Node: ec9e1c5be8de

Provenance: helper lemma. Research thread RT-1, OP-205 (arXiv:2610.15635, Theorems 1.3-1.4: eq(C_n^k) for k+1 = 2^m, n even, (k+1) not dividing n). Session 2026-11-06: a no-island route that needs only alternation and endpoint-only classes, not the consecutive-bit pairing (the pairing of the middle offsets is non-local, exp 17235). Experiments 17276 and 17282: with H, endpoint-only and no-island halves assumed at every root, an island in the class rooted at 0 is impossible already with guard 0 beyond its span at exponents 3 and 4, guard 2 at 5, guard 4 at 6 and 7; the only candidates at smaller guards are the offsets D/4, D/4+1, 3D/4-2, 3D/4-1.

Alignment conjecture. In a tight, exactly dyadically covered, fully covered integer Boolean class model at exponent m+1 (m ≥ 2) with m+2 active classes per vertex, alternating bit 1 and endpoint-only classes without bit 1, if for every class with bit 1 both its even-offset half and its odd-offset half have no island, then no class has an island (a < b < c with bit a missing, bit b selected, bit c missing).
-/

theorem cycle_power_dyadic_no_island_of_alternating_halves (m : ℕ) (hm : 2 ≤ m) (x : ℤ → ℕ → Bool)
    (htight : ∀ p, cycle_power_dyadic_class_weight (m+1) (x p) =
      (Finset.range (2^(m+1))).sum (fun a => (x p a).toNat))
    (hexact : ∀ j < (m+1), ∀ v : ℤ, (Finset.range (2^j)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^(m+1)-2^j)).toNat) = 1)
    (hcover : ∀ d : ℕ, 1 ≤ d → d < 2^(m+1) → ∀ v : ℤ,
      ∃ a : ℕ, a < 2^(m+1)-d ∧ x (v-(a : ℤ)) a = true ∧
        x (v-(a : ℤ)) (a+d) = true)
    (hcount : ∀ v : ℤ, (Finset.range (2^(m+1))).sum (fun a =>
      (x (v-(a : ℤ)) a).toNat) = (m+1)+1)
    (halt : ∀ p : ℤ, x (p+1) 1 = !x p 1)
    (hend : ∀ p : ℤ, x p 1 = false → ∀ j, 0 < j → j < 2^(m+1) - 1 → x p j = false)
    (hhalf : ∀ p : ℤ, x p 1 = true → ∀ e < 2, ∀ a b c : ℕ, a < b → b < c → c < 2^m →
      x p (2*a+e) = false → x p (2*b+e) = true → x p (2*c+e) = true) :
    ∀ (p : ℤ) (a b c : ℕ), a < b → b < c → c < 2^(m+1) →
      x p a = false → x p b = true → x p c = true := by
  intro p a b c hab hbc hc ha hb
  have hD : 2 ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; ring
  cases hp1 : x p 1
  · have := hend p hp1 b (by omega) (by omega)
    rw [this] at hb; exact absurd hb (by decide)
  · have hpar := cycle_power_dyadic_alternating_bit_one_parity x halt p hp1
    obtain ⟨ytight, yexact, -, -⟩ :=
      cycle_power_dyadic_alternating_half_model m hm x htight hexact hcover hcount halt hend p hp1 0
        (by norm_num)
    obtain ⟨ztight, zexact, -, -⟩ :=
      cycle_power_dyadic_alternating_half_model m hm x htight hexact hcover hcount halt hend p hp1 1
        (by norm_num)
    have hcr := cycle_power_dyadic_alternating_half_crossed_cover m x hcover halt hend p hp1
    have heq := cycle_power_dyadic_crossed_no_island_models_eq m (by omega)
      (fun q i => x (2 * q + p) (2 * i + 0)) (fun q i => x (2 * q + p) (2 * i + 1))
      ytight ztight yexact zexact
      (fun q a b c h1 h2 h3 h4 h5 => hhalf (2 * q + p) (hpar q).1 0 (by norm_num) a b c h1 h2 h3 h4 h5)
      (fun q a b c h1 h2 h3 h4 h5 => hhalf (2 * q + p) (hpar q).1 1 (by norm_num) a b c h1 h2 h3 h4 h5)
      hcr
    have hp0 : 2 * (0 : ℤ) + p = p := by ring
    have hpair : ∀ i < 2 ^ m, x p (2 * i) = x p (2 * i + 1) := by
      intro i hi
      have := heq 0 i hi
      simp only [hp0, Nat.add_zero] at this
      exact this
    have hxe : ∀ j < 2 ^ (m + 1), x p j = x p (2 * (j / 2) + 0) := by
      intro j hj
      rcases Nat.even_or_odd j with ⟨t, ht⟩ | ⟨t, ht⟩
      · rw [show j / 2 = t by omega, show 2 * t + 0 = j by omega]
      · rw [show j / 2 = t by omega, Nat.add_zero, hpair t (by omega), show 2 * t + 1 = j by omega]
    rw [hxe a (by omega)] at ha
    rw [hxe b (by omega)] at hb
    rw [hxe c hc]
    have hab2 : a / 2 < b / 2 := by
      rcases Nat.lt_or_ge (a / 2) (b / 2) with h' | h'
      · exact h'
      · rw [show a / 2 = b / 2 by omega, hb] at ha; exact absurd ha (by decide)
    rcases Nat.lt_or_ge (b / 2) (c / 2) with h' | h'
    · exact hhalf p hp1 0 (by norm_num) (a / 2) (b / 2) (c / 2) hab2 h' (by omega) ha hb
    · rw [show c / 2 = b / 2 by omega]; exact hb
