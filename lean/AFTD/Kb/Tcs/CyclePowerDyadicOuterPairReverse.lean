import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicExactEndpoints
import AFTD.Kb.Tcs.CyclePowerExactPairUnique
import AFTD.Kb.Tcs.CyclePowerDyadicBoundaryPairingAlternates

/-!
# cycle_power_dyadic_outer_pair_reverse

Topic: combinatorics   Node: 7075b850d3af

Provenance: helper lemma. Conditional outer pairing step for research thread RT-1 and OP-205, arXiv:2610.15635.

For exponent m at least three, consider a Boolean integer-indexed dyadic class model with exact dyadic ownership at every rank, coverage of every ordinary distance below 2^m, equal boundary bits at offsets 1 and 2^m-2, and only endpoints selected in every class whose bit 1 is false. If a class selects offsets 1 and 2, it also selects offset 3.
-/

theorem cycle_power_dyadic_outer_pair_reverse (m : ℕ) (hm : 3 ≤ m) (x : ℤ → ℕ → Bool)
    (hexact : ∀ j < m, ∀ v : ℤ, (Finset.range (2^j)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^m-2^j)).toNat) = 1)
    (hcover : ∀ d : ℕ, 1 ≤ d → d < 2^m → ∀ v : ℤ,
      ∃ a : ℕ, a < 2^m-d ∧ x (v-(a : ℤ)) a = true ∧
        x (v-(a : ℤ)) (a+d) = true)
    (h1 : ∀ p : ℤ, x p 1 = x p (2^m-2))
    (hend : ∀ p : ℤ, x p 1 = false → ∀ j, 0 < j → j < 2^m-1 → x p j = false) :
    ∀ p : ℤ, x p 1 = true → x p 2 = true → x p 3 = true := by
  have hD : 8 ≤ 2^m := by
    calc 8 = 2^3 := by norm_num
      _ ≤ 2^m := Nat.pow_le_pow_right (by norm_num) hm
  have ends := cycle_power_dyadic_exact_endpoints m (by omega) x hexact
  have alt := cycle_power_dyadic_boundary_pairing_alternates m (by omega) x hexact h1
  have ex4 : ∀ v : ℤ, (Finset.range 4).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^m-4)).toNat) = 1 := by
    simpa using hexact 2 (by omega)
  intro p hbit h2
  by_contra h3'
  have h3 : x p 3 = false := Bool.eq_false_of_not_eq_true h3'
  have hp1 : x (p+1) 1 = false := by rw [alt p, hbit]; rfl
  have hp2 : x (p+2) 1 = true := by
    have h := alt (p+1)
    rw [show p+1+1 = p+2 by ring, hp1] at h
    exact h
  have hp3 : x (p+3) 1 = false := by
    have h := alt (p+2)
    rw [show p+2+1 = p+3 by ring, hp2] at h
    exact h
  have hm1 : x (p-1) 1 = false := by
    have h := alt (p-1)
    rw [show p-1+1 = p by ring, hbit] at h
    cases hb : x (p-1) 1 <;> simp [hb] at h ⊢
  have hp2high : x (p+2) (2^m-4) = false := by
    by_contra hn
    have hx : x (p+2) (2^m-4) = true := Bool.eq_true_of_not_eq_false hn
    have eq := cycle_power_exact_pair_unique (2^m) 4 x ex4 (p+2) 0 2 (by omega) (by omega)
      (by simpa using (ends (p+2)).1) (by simpa using hx)
      (by simpa using h2)
      (by simpa [show 2 + 2^m - 4 = 2^m - 2 by omega, ← h1 p] using hbit)
    omega
  obtain ⟨a, ha, ha1, ha2⟩ := hcover (2^m-5) (by omega) (by omega) (p+3)
  have ha' : a < 5 := by omega
  interval_cases a
  · have hh : x (p+3) (2^m-5) = true := by simpa using ha2
    have hh' := hend (p+3) hp3 (2^m-5) (by omega) (by omega)
    rw [hh'] at hh; contradiction
  · have hh : x (p+2) (2^m-4) = true := by
      simpa [show p+3-1 = p+2 by ring, show 1 + (2^m-5) = 2^m-4 by omega] using ha2
    rw [hp2high] at hh; contradiction
  · have hh : x (p+1) 2 = true := by simpa [show p+3-2 = p+1 by ring] using ha1
    have hh' := hend (p+1) hp1 2 (by omega) (by omega)
    rw [hh'] at hh; contradiction
  · have hh : x p 3 = true := by simpa using ha1
    rw [h3] at hh; contradiction
  · have hh : x (p-1) 4 = true := by simpa [show p+3-4 = p-1 by ring] using ha1
    have hh' := hend (p-1) hm1 4 (by omega) (by omega)
    rw [hh'] at hh; contradiction
