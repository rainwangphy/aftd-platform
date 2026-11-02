import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicExactEndpoints
import AFTD.Kb.Tcs.CyclePowerExactPairUnique
import AFTD.Kb.Tcs.CyclePowerDyadicBoundaryPairingAlternates

/-!
# cycle_power_dyadic_outer_pair_forward

Topic: combinatorics   Node: 2ff5a9141d50

Provenance: helper lemma. RT-1, OP-205, arXiv:2610.15635; auxiliary rigidity lemmas for the dyadic cycle-power covering problem.

In a fully covered exact dyadic Boolean class model with exponent at least three and matching boundary bits in every class, if a class selects offsets 1 and 3 it also selects offset 2.
-/

theorem cycle_power_dyadic_outer_pair_forward (m : ℕ) (hm : 3 ≤ m) (x : ℤ → ℕ → Bool)
    (hexact : ∀ j < m, ∀ v : ℤ, (Finset.range (2^j)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^m-2^j)).toNat) = 1)
    (hcover : ∀ d : ℕ, 1 ≤ d → d < 2^m → ∀ v : ℤ,
      ∃ a : ℕ, a < 2^m-d ∧ x (v-(a : ℤ)) a = true ∧
        x (v-(a : ℤ)) (a+d) = true)
    (h1 : ∀ p : ℤ, x p 1 = x p (2^m-2)) :
    ∀ p : ℤ, x p 1 = true → x p 3 = true → x p 2 = true := by
  have hD : 8 ≤ 2^m := by
    calc 8 = 2^3 := by norm_num
      _ ≤ 2^m := Nat.pow_le_pow_right (by norm_num) hm
  have ends := cycle_power_dyadic_exact_endpoints m (by omega) x hexact
  have alt := cycle_power_dyadic_boundary_pairing_alternates m (by omega) x hexact h1
  have ex4 : ∀ v : ℤ, (Finset.range 4).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^m-4)).toNat) = 1 := by
    simpa using hexact 2 (by omega)
  intro p hbit h3
  by_contra h2'
  have h2 : x p 2 = false := Bool.eq_false_of_not_eq_true h2'
  have hp1 : x (p+1) 1 = false := by rw [alt p, hbit]; rfl
  have hp2 : x (p+2) 1 = true := by
    have h := alt (p+1)
    rw [show p+1+1 = p+2 by ring, hp1] at h
    exact h
  have hp21 : x (p+2) (2^m-3) = false := by
    by_contra hn
    have hx : x (p+2) (2^m-3) = true := Bool.eq_true_of_not_eq_false hn
    have eq := cycle_power_exact_pair_unique (2^m) 4 x ex4 (p+3) 1 3 (by omega) (by omega)
      (by simpa [show p+3-1 = p+2 by ring] using hp2)
      (by simpa [show p+3-1 = p+2 by ring, show 1 + 2^m - 4 = 2^m - 3 by omega] using hx)
      (by simpa using h3) (by simpa [show 3 + 2^m - 4 = 2^m - 1 by omega] using (ends p).2)
    omega
  obtain ⟨a, ha, ha1, ha2⟩ := hcover (2^m-3) (by omega) (by omega) (p+2)
  have ha' : a < 3 := by omega
  interval_cases a
  · have hh : x (p+2) (2^m-3) = true := by simpa using ha2
    rw [hp21] at hh; contradiction
  · have hh : x (p+1) 1 = true := by simpa [show p+2-1 = p+1 by ring] using ha1
    rw [hp1] at hh; contradiction
  · have hh : x p 2 = true := by simpa using ha1
    rw [h2] at hh; contradiction
