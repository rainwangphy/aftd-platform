import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicNoIslandOfAlternatingEndpoint
import AFTD.Kb.Tcs.CyclePowerFifteenModelNoIsland
import AFTD.Kb.Tcs.SimpleGraphEquivalenceCoveringNumberCyclePowerThreeOfModFourEqTwo
import AFTD.Kb.Tcs.SimpleGraphEquivalenceCoveringNumberCyclePowerSevenOfNotDvd
import AFTD.Kb.Tcs.SimpleGraphEquivalenceCoveringNumberCyclePowerDyadicOfClassShape
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.SimpleGraphEquivalenceCoveringNumber
import AFTD.Kb.Tcs.SimpleGraphCyclePower

/-!
# simple_graph_equivalence_covering_number_cycle_power_two_pow_even_not_dvd_of_alternating_endpoint

Topic: combinatorics   Node: 8536a47d878c

Provenance: helper lemma. Research thread RT-1, OP-205 (arXiv:2610.15635, Theorems 1.3-1.4: eq(C_n^k) for k+1 = 2^m, n even, (k+1) not dividing n). Session 2026-11-06: a no-island route that needs only alternation and endpoint-only classes, not the consecutive-bit pairing (the pairing of the middle offsets is non-local, exp 17235).

Conditional reduction of OP-205 to alternation and endpoint-only classes: if for every m ≥ 5 every tight, exactly dyadically covered, fully covered model at exponent m with m+1 active classes per vertex has alternating bit 1 and endpoint-only classes without bit 1, then eq(C_n^k) = m+2 for k+1 = 2^m, n even, n ≥ max(2k+2, k²(k+2)), (k+1) not dividing n. Weaker hypothesis than ..._of_alternating_paired: no consecutive-bit pairing.
-/

theorem simple_graph_equivalence_covering_number_cycle_power_two_pow_even_not_dvd_of_alternating_endpoint
    (hstruct : ∀ m : ℕ, 5 ≤ m → ∀ (x : ℤ → ℕ → Bool),
      (∀ p, cycle_power_dyadic_class_weight m (x p) =
        (Finset.range (2^m)).sum (fun a => (x p a).toNat)) →
      (∀ j < m, ∀ v : ℤ, (Finset.range (2^j)).sum (fun a =>
        (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^m-2^j)).toNat) = 1) →
      (∀ d : ℕ, 1 ≤ d → d < 2^m → ∀ v : ℤ,
        ∃ a : ℕ, a < 2^m-d ∧ x (v-(a : ℤ)) a = true ∧
          x (v-(a : ℤ)) (a+d) = true) →
      (∀ v : ℤ, (Finset.range (2^m)).sum (fun a =>
        (x (v-(a : ℤ)) a).toNat) = m+1) →
      (∀ p : ℤ, x (p+1) 1 = !x p 1) ∧
      (∀ p : ℤ, x p 1 = false → ∀ j, 0 < j → j < 2^m - 1 → x p j = false))
    (k m n : ℕ) (hm : 1 ≤ m) (hkm : k + 1 = 2 ^ m)
    (hn : max (2 * k + 2) (k ^ 2 * (k + 2)) ≤ n) (hev : Even n) (hnd : ¬ (k + 1) ∣ n) :
    simple_graph_equivalence_covering_number (simple_graph_cycle_power n k) = m + 2 := by
  have key : ∀ t : ℕ, 4 ≤ t → (∀ (y : ℤ → ℕ → Bool),
      (∀ p, cycle_power_dyadic_class_weight t (y p) =
        (Finset.range (2^t)).sum (fun a => (y p a).toNat)) →
      (∀ j < t, ∀ v : ℤ, (Finset.range (2^j)).sum (fun a =>
        (y (v-(a : ℤ)) a && y (v-(a : ℤ)) (a+2^t-2^j)).toNat) = 1) →
      (∀ d : ℕ, 1 ≤ d → d < 2^t → ∀ v : ℤ,
        ∃ a : ℕ, a < 2^t-d ∧ y (v-(a : ℤ)) a = true ∧
          y (v-(a : ℤ)) (a+d) = true) →
      (∀ v : ℤ, (Finset.range (2^t)).sum (fun a =>
        (y (v-(a : ℤ)) a).toNat) = t+1) →
      ∀ (p : ℤ) (a b c : ℕ), a < b → b < c → c < 2^t →
        y p a = false → y p b = true → y p c = true) := by
    intro t ht4
    induction t, ht4 using Nat.le_induction with
    | base => exact cycle_power_fifteen_model_no_island
    | succ t ht4 ih =>
      intro y htight hexact hcover hcount
      obtain ⟨halt, hend⟩ := hstruct (t+1) (by omega) y htight hexact hcover hcount
      exact cycle_power_dyadic_no_island_of_alternating_endpoint t (by omega) ih y htight hexact hcover
        hcount halt hend
  have hnA : 2 * k + 2 ≤ n := (le_max_left _ _).trans hn
  have hnB : k ^ 2 * (k + 2) ≤ n := (le_max_right _ _).trans hn
  rcases (show m = 1 ∨ m = 2 ∨ m = 3 ∨ 4 ≤ m by omega) with rfl | rfl | rfl | h4
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
  · exact simple_graph_equivalence_covering_number_cycle_power_dyadic_of_class_shape k m n hm hkm hn hev hnd
      (key m h4)
