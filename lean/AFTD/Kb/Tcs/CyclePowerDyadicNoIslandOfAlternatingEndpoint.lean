import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicAlternatingHalfModel
import AFTD.Kb.Tcs.CyclePowerDyadicNoIslandOfAlternatingHalves
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight

/-!
# cycle_power_dyadic_no_island_of_alternating_endpoint

Topic: combinatorics   Node: b0a727d72e65

Provenance: helper lemma. Research thread RT-1, OP-205 (arXiv:2610.15635, Theorems 1.3-1.4: eq(C_n^k) for k+1 = 2^m, n even, (k+1) not dividing n). Session 2026-11-06: a no-island route that needs only alternation and endpoint-only classes, not the consecutive-bit pairing (the pairing of the middle offsets is non-local, exp 17235).

Induction step without pairing. If every model at exponent m (m ≥ 2) has no island, then every tight, exactly dyadically covered, fully covered model at exponent m+1 with m+2 active classes per vertex, alternating bit 1 and endpoint-only classes without bit 1, has no island. Unlike cycle_power_dyadic_no_island_of_alternating_paired it does not assume the consecutive-bit pairing.
-/

theorem cycle_power_dyadic_no_island_of_alternating_endpoint (m : ℕ) (hm : 2 ≤ m)
    (hshape : ∀ (y : ℤ → ℕ → Bool),
      (∀ p, cycle_power_dyadic_class_weight m (y p) =
        (Finset.range (2^m)).sum (fun a => (y p a).toNat)) →
      (∀ j < m, ∀ v : ℤ, (Finset.range (2^j)).sum (fun a =>
        (y (v-(a : ℤ)) a && y (v-(a : ℤ)) (a+2^m-2^j)).toNat) = 1) →
      (∀ d : ℕ, 1 ≤ d → d < 2^m → ∀ v : ℤ,
        ∃ a : ℕ, a < 2^m-d ∧ y (v-(a : ℤ)) a = true ∧
          y (v-(a : ℤ)) (a+d) = true) →
      (∀ v : ℤ, (Finset.range (2^m)).sum (fun a =>
        (y (v-(a : ℤ)) a).toNat) = m+1) →
      ∀ (p : ℤ) (a b c : ℕ), a < b → b < c → c < 2^m →
        y p a = false → y p b = true → y p c = true)
    (x : ℤ → ℕ → Bool)
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
    (hend : ∀ p : ℤ, x p 1 = false → ∀ j, 0 < j → j < 2^(m+1) - 1 → x p j = false) :
    ∀ (p : ℤ) (a b c : ℕ), a < b → b < c → c < 2^(m+1) →
      x p a = false → x p b = true → x p c = true := by
  apply cycle_power_dyadic_no_island_of_alternating_halves m hm x htight hexact hcover hcount halt hend
  intro p hp1 e he a b c h1 h2 h3 h4 h5
  obtain ⟨t, ex, cv, cn⟩ :=
    cycle_power_dyadic_alternating_half_model m hm x htight hexact hcover hcount halt hend p hp1 e he
  have hp0 : 2 * (0 : ℤ) + p = p := by ring
  have := hshape (fun q b => x (2 * q + p) (2 * b + e)) t ex cv cn 0 a b c h1 h2 h3
  simp only [hp0] at this
  exact this h4 h5
