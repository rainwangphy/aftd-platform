import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicCentralPositionExists
import AFTD.Kb.Tcs.PeriodicDyadicDvdOfHalfShiftNe
import AFTD.Kb.Tcs.CyclePowerClassLabelPeriodOfBoundedEndpointOverlap
import AFTD.Kb.Tcs.CyclePowerDyadicModelDvdOfLabelPeriod
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight

/-!
# cycle_power_dyadic_model_dvd_of_endpoint_overlap

Topic: combinatorics   Node: 4e6c7e97aa3b

Provenance: helper lemma. Uniform helpers for OP-205 / RT-1 following arXiv:2610.15635, Section 3. The neighbour-weight induction and central occurrence are class-model helpers; they do not prove the unresolved covering number. No research advance is claimed.

A periodic optimal dyadic class model whose old active classes intersect the next endpoint class has period divisible by the dyadic radius. The overlap condition remains an explicit hypothesis.
-/

open Finset

theorem cycle_power_dyadic_model_dvd_of_endpoint_overlap
    (m n : ℕ) (hm : 2 ≤ m) (hn : 0 < n)
    (x : ℤ → ℕ → Bool) (ell : ℤ → Fin (m+1))
    (hperiod : ∀ p a, x (p+(n : ℤ)) a = x p a)
    (hell : ∀ p, ell (p+(n : ℤ)) = ell p)
    (htight : ∀ p, cycle_power_dyadic_class_weight m (x p) =
      (range (2^m)).sum (fun a => (x p a).toNat))
    (hcount : ∀ v : ℤ, (range (2^m)).sum
      (fun a => (x (v-(a : ℤ)) a).toNat) = m+1)
    (hexact : ∀ j < m, ∀ v : ℤ, (range (2^j)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^m-2^j)).toNat) = 1)
    (hcover : ∀ d : ℕ, 1 ≤ d → d < 2^m → ∀ v : ℤ,
      ∃ a : ℕ, a < 2^m-d ∧ x (v-(a : ℤ)) a = true ∧
        x (v-(a : ℤ)) (a+d) = true)
    (hsep : ∀ (v : ℤ) (a b : ℕ), a < 2^m → b < 2^m → a ≠ b →
      x (v-(a : ℤ)) a = true → x (v-(b : ℤ)) b = true →
        ell (v-(a : ℤ)) ≠ ell (v-(b : ℤ)))
    (hoverlap : ∀ (p : ℤ) (q : ℕ), 1 ≤ q → q < 2^m →
      x (p+(q : ℤ)) (2^m-1-q) = true →
      ∃ a : ℕ, a < q ∧ x (p+(q : ℤ)) (2^m-q+a) = true ∧
        x (p+((2^m : ℕ) : ℤ)) a = true) :
    2^m ∣ n := by
  have hlabel := cycle_power_class_label_period_of_bounded_endpoint_overlap
    (2^m) (m+1) x ell hcount hsep hoverlap
  apply cycle_power_dyadic_model_dvd_of_label_period m n hm hn x ell
    hperiod hell hlabel htight hexact _ hsep
  intro j hj0 hj v
  have hjp : 2^j ≤ 2^(m-1) := Nat.pow_le_pow_right (by decide) (by omega)
  have hpow : 2^m=2*2^(m-1) := by
    conv_lhs => rw [show m=(m-1)+1 by omega]
    rw [pow_succ]; omega
  have htwo : 2 ≤ 2^(m-1) := by
    calc 2 = 2^1 := rfl
         _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)
  have hdpos : 1 ≤ 2^m-2^j-1 := by rw [hpow]; omega
  have hdlt : 2^m-2^j-1 < 2^m :=
    lt_of_le_of_lt (Nat.sub_le _ _)
      (Nat.sub_lt (Nat.two_pow_pos m) (Nat.two_pow_pos j))
  obtain ⟨a, ha, hx0, hx1⟩ := hcover (2^m-2^j-1) hdpos hdlt v
  have hlarge : 2^j+1 ≤ 2^m := by rw [hpow]; omega
  have hrange : 2^m-(2^m-2^j-1)=2^j+1 := by omega
  rw [hrange] at ha
  refine ⟨a, ha, hx0, ?_⟩
  have hi : a+2^m-2^j-1=a+(2^m-2^j-1) := by omega
  rw [hi]
  exact hx1
