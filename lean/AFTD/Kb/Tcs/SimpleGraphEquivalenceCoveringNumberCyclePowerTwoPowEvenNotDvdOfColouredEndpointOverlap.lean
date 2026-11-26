import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphEquivalenceCoveringNumberCyclePowerDyadicOfClassShape
import AFTD.Kb.Tcs.CyclePowerDyadicModelDvdOfEndpointOverlap
import AFTD.Kb.Tcs.SimpleGraphEquivalenceCoveringNumberCyclePowerFifteenOfNotDvd
import AFTD.Kb.Tcs.SimpleGraphEquivalenceCoveringNumberCyclePowerThirtyOneOfNotDvd
import AFTD.Kb.Tcs.SimpleGraphEquivalenceCoveringNumberCyclePowerSevenOfNotDvd
import AFTD.Kb.Tcs.SimpleGraphEquivalenceCoveringNumberCyclePowerThreeOfModFourEqTwo
import AFTD.Kb.Tcs.SimpleGraphCyclePowerDyadicCoverClassModel
import AFTD.Kb.Tcs.SimpleGraphHasEquivalenceCoverCyclePowerDyadicUpper
import AFTD.Kb.Tcs.SimpleGraphHasEquivalenceCoverMono
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.SimpleGraphEquivalenceCoveringNumber
import AFTD.Kb.Tcs.SimpleGraphCyclePower
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.SimpleGraphHasEquivalenceCover

/-!
# simple_graph_equivalence_covering_number_cycle_power_two_pow_even_not_dvd_of_coloured_endpoint_overlap

Topic: combinatorics   Node: b666c0cc468b

Provenance: helper lemma. Helper assembly for the main statement of OP-205 (arXiv:2610.15635, the case k+1 = 2^m, n even, (k+1) not dividing n, left open there): reduces it to the endpoint-overlap property, which may now use periodicity and the colouring of the classes; the property itself is not proved here.

Conditional reduction of OP-205 to endpoint overlap in periodic coloured class models at exponents m ≥ 6. Suppose that for every m ≥ 6 and every n-periodic tight, exactly dyadically covered, fully covered integer Boolean class model at exponent m with m+1 active classes per vertex, together with an n-periodic labelling of the classes by m+1 colours that separates any two classes through a common vertex, every class other than the ending one that is active at the last vertex of the class rooted at p shares a vertex with the class rooted at p+2^m. Then eq(C_n^k) = m+2 for k+1 = 2^m, m ≥ 1, n even, n ≥ max(2k+2, k²(k+2)), (k+1) not dividing n. The cases m ≤ 5 use the proved theorems for k = 3, 7, 15, 31.
-/

theorem simple_graph_equivalence_covering_number_cycle_power_two_pow_even_not_dvd_of_coloured_endpoint_overlap
    (hoverlap : ∀ m : ℕ, 6 ≤ m → ∀ n : ℕ, 0 < n →
      ∀ (x : ℤ → ℕ → Bool) (ell : ℤ → Fin (m+1)),
      (∀ p a, x (p+(n : ℤ)) a = x p a) →
      (∀ p, ell (p+(n : ℤ)) = ell p) →
      (∀ p, cycle_power_dyadic_class_weight m (x p) =
        (Finset.range (2^m)).sum (fun a => (x p a).toNat)) →
      (∀ v : ℤ, (Finset.range (2^m)).sum
        (fun a => (x (v-(a : ℤ)) a).toNat) = m+1) →
      (∀ j < m, ∀ v : ℤ, (Finset.range (2^j)).sum (fun a =>
        (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^m-2^j)).toNat) = 1) →
      (∀ d : ℕ, 1 ≤ d → d < 2^m → ∀ v : ℤ,
        ∃ a : ℕ, a < 2^m-d ∧ x (v-(a : ℤ)) a = true ∧
          x (v-(a : ℤ)) (a+d) = true) →
      (∀ (v : ℤ) (a b : ℕ), a < 2^m → b < 2^m → a ≠ b →
        x (v-(a : ℤ)) a = true → x (v-(b : ℤ)) b = true →
          ell (v-(a : ℤ)) ≠ ell (v-(b : ℤ))) →
      ∀ (p : ℤ) (q : ℕ), 1 ≤ q → q < 2^m →
        x (p+(q : ℤ)) (2^m-1-q) = true →
        ∃ a : ℕ, a < q ∧ x (p+(q : ℤ)) (2^m-q+a) = true ∧
          x (p+((2^m : ℕ) : ℤ)) a = true)
    (k m n : ℕ) (hm : 1 ≤ m) (hkm : k + 1 = 2 ^ m)
    (hn : max (2 * k + 2) (k ^ 2 * (k + 2)) ≤ n) (hev : Even n) (hnd : ¬ (k + 1) ∣ n) :
    simple_graph_equivalence_covering_number (simple_graph_cycle_power n k) = m + 2 := by
  have hnA : 2 * k + 2 ≤ n := (le_max_left _ _).trans hn
  have hnB : k ^ 2 * (k + 2) ≤ n := (le_max_right _ _).trans hn
  rcases (show m = 1 ∨ m = 2 ∨ m = 3 ∨ m = 4 ∨ m = 5 ∨ 6 ≤ m by omega) with
    rfl | rfl | rfl | rfl | rfl | h6
  · refine simple_graph_equivalence_covering_number_cycle_power_dyadic_of_class_shape k 1 n hm hkm hn hev hnd ?_
    intro y _ _ _ _ p a b c hab hbc hc
    norm_num at hc
    omega
  · have hk : k = 3 := by norm_num at hkm; omega
    subst hk
    have h4n : n % 4 = 2 := by
      obtain ⟨r, hr⟩ := hev
      omega
    exact simple_graph_equivalence_covering_number_cycle_power_three_of_mod_four_eq_two n (by norm_num at hnB; omega) h4n
  · have hk : k = 7 := by norm_num at hkm; omega
    subst hk
    exact simple_graph_equivalence_covering_number_cycle_power_seven_of_not_dvd n (by norm_num at hnB; omega)
      (by simpa using hnd)
  · have hk : k = 15 := by norm_num at hkm; omega
    subst hk
    exact simple_graph_equivalence_covering_number_cycle_power_fifteen_of_not_dvd n (by norm_num at hnB; omega) hev
      (by simpa using hnd)
  · have hk : k = 31 := by norm_num at hkm; omega
    subst hk
    exact simple_graph_equivalence_covering_number_cycle_power_thirty_one_of_not_dvd n (by norm_num at hnB; omega) hev
      (by simpa using hnd)
  · have hm2 : 2 ≤ m := by omega
    have hD4 : 4 ≤ 2^m := by
      calc
        4 = 2^2 := by decide
        _ ≤ 2^m := Nat.pow_le_pow_right (by decide) hm2
    have hk3 : 3 ≤ k := by omega
    have hnB2 : 2*k^2 ≤ n := by
      calc
        2*k^2 = k^2*2 := by ring
        _ ≤ k^2*(k+2) := Nat.mul_le_mul_left (k^2) (by omega)
        _ ≤ n := hnB
    have hnu : max (2*k+2) (2*k^2) ≤ n := max_le_iff.mpr ⟨hnA, hnB2⟩
    have hupper := simple_graph_has_equivalence_cover_cycle_power_dyadic_upper k m n (by omega) hkm hnu
    letI : NeZero n := ⟨by omega⟩
    refine le_antisymm (Nat.sInf_le hupper) (le_csInf ⟨m+2, hupper⟩ fun t ht => ?_)
    by_contra hbad
    have htle : t ≤ m+1 := by omega
    obtain ⟨c, hc, hcov⟩ := simple_graph_has_equivalence_cover_mono
      (simple_graph_cycle_power n k) htle ht
    have hkD : k=2^m-1 := by omega
    have hn3k : 3*k+1 ≤ n := by
      have hsq := Nat.mul_le_mul_right k hk3
      nlinarith [hnB2]
    have hn3 : 3*(2^m-1)+1 ≤ n := by simpa only [← hkD] using hn3k
    rw [hkD] at hc hcov
    obtain ⟨x, ell, hxp, hep, hends, htw, hct, hex, hcv, hfaith, hsep⟩ :=
      simple_graph_cycle_power_dyadic_cover_class_model m n (by omega) hn3 c hc hcov
    have hov := hoverlap m h6 n (by omega) x ell hxp hep htw hct hex hcv hsep
    have hdvd := cycle_power_dyadic_model_dvd_of_endpoint_overlap m n hm2 (by omega) x ell
      hxp hep htw hct hex hcv hsep hov
    apply hnd
    simpa only [hkm] using hdvd
