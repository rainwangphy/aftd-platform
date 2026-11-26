import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphEquivalenceCoveringNumberCyclePowerDyadicOfClassShape
import AFTD.Kb.Tcs.CyclePowerDyadicNoIslandOfMiddleFullPrune
import AFTD.Kb.Tcs.SimpleGraphEquivalenceCoveringNumberCyclePowerFifteenOfNotDvd
import AFTD.Kb.Tcs.SimpleGraphEquivalenceCoveringNumberCyclePowerThirtyOneOfNotDvd
import AFTD.Kb.Tcs.SimpleGraphEquivalenceCoveringNumberCyclePowerSevenOfNotDvd
import AFTD.Kb.Tcs.SimpleGraphEquivalenceCoveringNumberCyclePowerThreeOfModFourEqTwo
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeightLe
import AFTD.Kb.Tcs.SimpleGraphEquivalenceCoveringNumber
import AFTD.Kb.Tcs.SimpleGraphCyclePower

/-!
# simple_graph_equivalence_covering_number_cycle_power_two_pow_even_not_dvd_of_middle_island

Topic: combinatorics   Node: 0f4e5c2f01e3

Provenance: helper lemma. Helper step for the main statement of OP-205 (arXiv:2610.15635, the case k+1 = 2^m, n even, (k+1) not dividing n, left open there); it concerns the integer Boolean class models that optimal (m+1)-layer covers give. Assembly: the two hypotheses give middle fullness, hence no selected island (cycle_power_dyadic_no_island_of_middle_full_prune), hence the covering number (the class-shape conditional). The hypotheses are the stated cycle_power_dyadic_middle_offset_outer_full_or_island and cycle_power_dyadic_optimal_count_no_middle_island; they are not proved here.

Conditional reduction of OP-205 to two statements about class models at exponents j+3 ≥ 6, with D = 2^(j+3), g = 2^j. Suppose (1), without any vertex count: in every tight, exactly dyadically covered, fully covered integer Boolean class model, a class containing an offset in [D/4, 3D/4) contains [0, D/4) and [3D/4, D) completely or is exactly the island [0, g) ∪ [3g, 5g) ∪ [7g, D); and (2): when moreover every vertex lies in exactly j+4 classes, no class is that island. Then eq(C_n^k) = m+2 for k+1 = 2^m, m ≥ 1, n even, n ≥ max(2k+2, k²(k+2)), (k+1) not dividing n. The cases m ≤ 5 use the proved theorems for k = 3, 7, 15, 31.
-/

theorem simple_graph_equivalence_covering_number_cycle_power_two_pow_even_not_dvd_of_middle_island
    (hfull : ∀ j : ℕ, 3 ≤ j → ∀ (x : ℤ → ℕ → Bool),
      (∀ p, cycle_power_dyadic_class_weight (j+3) (x p) =
        (Finset.range (2^(j+3))).sum (fun a => (x p a).toNat)) →
      (∀ i < j+3, ∀ v : ℤ, (Finset.range (2^i)).sum (fun a =>
        (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^(j+3)-2^i)).toNat) = 1) →
      (∀ d : ℕ, 1 ≤ d → d < 2^(j+3) → ∀ v : ℤ,
        ∃ a : ℕ, a < 2^(j+3)-d ∧ x (v-(a : ℤ)) a = true ∧
          x (v-(a : ℤ)) (a+d) = true) →
      ∀ (p : ℤ) (a : ℕ), 2^(j+1) ≤ a → a < 3*2^(j+1) → x p a = true →
        (∀ i < 2^(j+1), x p i = true ∧ x p (i + 3*2^(j+1)) = true) ∨
        (∀ b < 2^(j+3), x p b =
          (decide (b < 2^j) || (decide (3*2^j ≤ b) && decide (b < 5*2^j)) || decide (7*2^j ≤ b))))
    (hisland : ∀ j : ℕ, 3 ≤ j → ∀ (x : ℤ → ℕ → Bool),
      (∀ p, cycle_power_dyadic_class_weight (j+3) (x p) =
        (Finset.range (2^(j+3))).sum (fun a => (x p a).toNat)) →
      (∀ i < j+3, ∀ v : ℤ, (Finset.range (2^i)).sum (fun a =>
        (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^(j+3)-2^i)).toNat) = 1) →
      (∀ d : ℕ, 1 ≤ d → d < 2^(j+3) → ∀ v : ℤ,
        ∃ a : ℕ, a < 2^(j+3)-d ∧ x (v-(a : ℤ)) a = true ∧
          x (v-(a : ℤ)) (a+d) = true) →
      (∀ v : ℤ, (Finset.range (2^(j+3))).sum (fun a =>
        (x (v-(a : ℤ)) a).toNat) = (j+3)+1) →
      ∀ p : ℤ, ¬ ∀ b < 2^(j+3), x p b =
        (decide (b < 2^j) || (decide (3*2^j ≤ b) && decide (b < 5*2^j)) || decide (7*2^j ≤ b)))
    (k m n : ℕ) (hm : 1 ≤ m) (hkm : k + 1 = 2 ^ m)
    (hn : max (2 * k + 2) (k ^ 2 * (k + 2)) ≤ n) (hev : Even n) (hnd : ¬ (k + 1) ∣ n) :
    simple_graph_equivalence_covering_number (simple_graph_cycle_power n k) = m + 2 := by
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
  · obtain ⟨j, rfl⟩ : ∃ j, m = j + 3 := ⟨m - 3, by omega⟩
    have hj : 3 ≤ j := by omega
    refine simple_graph_equivalence_covering_number_cycle_power_dyadic_of_class_shape k (j+3) n hm hkm hn hev hnd ?_
    intro x htight hexact hcover hcount
    have hmid : ∀ (p : ℤ) (a : ℕ), 2^(j+1) ≤ a → a < 3*2^(j+1) → x p a = true →
        ∀ i < 2^(j+1+1), cycle_power_dyadic_b_lift (j+1) (x p) i = true := by
      intro p a ha1 ha2 hxa i hi
      rcases hfull j hj x htight hexact hcover p a ha1 ha2 hxa with hF | hI
      · unfold cycle_power_dyadic_b_lift
        by_cases h : i < 2^(j+1)
        · rw [if_pos h]; exact (hF i h).1
        · rw [if_neg h]
          have h2 : (2:ℕ)^(j+1+1) = 2 * 2^(j+1) := by rw [pow_succ]; ring
          have e : i + 2^(j+1+1) = (i - 2^(j+1)) + 3*2^(j+1) := by omega
          rw [e]
          exact (hF (i - 2^(j+1)) (by omega)).2
      · exact absurd hI (hisland j hj x htight hexact hcover hcount p)
    exact cycle_power_dyadic_no_island_of_middle_full_prune (j+1) x htight hexact hmid hcover
