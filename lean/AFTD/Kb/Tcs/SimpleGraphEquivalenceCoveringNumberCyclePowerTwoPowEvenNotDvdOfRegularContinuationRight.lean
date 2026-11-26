import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphEquivalenceCoveringNumberCyclePowerTwoPowEvenNotDvdOfRegularContinuation
import AFTD.Kb.Tcs.CyclePowerDyadicRegularContinuationLeftOfRight
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.SimpleGraphEquivalenceCoveringNumber
import AFTD.Kb.Tcs.SimpleGraphCyclePower

/-!
# simple_graph_equivalence_covering_number_cycle_power_two_pow_even_not_dvd_of_regular_continuation_right

Topic: combinatorics   Node: 0c6ce506b800

Provenance: helper lemma. Helper step for the main statement of OP-205 (arXiv:2610.15635, the case k+1 = 2^m, n even, (k+1) not dividing n, left open there); it concerns the integer Boolean class models that optimal (m+1)-layer covers give. Final assembly of the 2026-11-26 ladder: the hypotheses are the stated cycle_power_dyadic_middle_offset_outer_full_or_island, cycle_power_dyadic_middle_island_regular_neighbourhood and cycle_power_dyadic_regular_continuation_right, none proved here.

Conditional reduction of OP-205 to three statements about tight, exactly dyadically covered, fully covered integer Boolean class models. Call a class regular of the first kind if it contains offset 1 and its offsets come in consecutive pairs (2i, 2i+1 both in or both out), and regular of the second kind if it consists of its two endpoints only. (hfull) without any count, at exponent j+3 ≥ 6 with D = 2^(j+3), g = 2^j: a class containing an offset in [D/4, 3D/4) contains [0, D/4) and [3D/4, D) completely or is exactly the island [0, g) ∪ [3g, 5g) ∪ [7g, D). (hIR) without any count, at exponent j+3 ≥ 4: an island class rooted at p forces every class rooted within 7g of p to be regular, of the first kind at even distance and of the second kind at odd distance. (hCTr) with exactly t+2 active classes per vertex at exponent t+1 ≥ 4: if the classes on the 3·2^t roots ending at p0 are regular with alternating kinds and p0 of the first kind, the classes rooted at p0+1 and p0+2 are regular, of the second and first kind. Then eq(C_n^k) = m+2 for k+1 = 2^m, m ≥ 1, n even, n ≥ max(2k+2, k²(k+2)), (k+1) not dividing n.
-/

theorem simple_graph_equivalence_covering_number_cycle_power_two_pow_even_not_dvd_of_regular_continuation_right
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
    (hIR : ∀ j : ℕ, 1 ≤ j → ∀ (x : ℤ → ℕ → Bool),
      (∀ p, cycle_power_dyadic_class_weight (j+3) (x p) =
        (Finset.range (2^(j+3))).sum (fun a => (x p a).toNat)) →
      (∀ i < j+3, ∀ v : ℤ, (Finset.range (2^i)).sum (fun a =>
        (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^(j+3)-2^i)).toNat) = 1) →
      (∀ d : ℕ, 1 ≤ d → d < 2^(j+3) → ∀ v : ℤ,
        ∃ a : ℕ, a < 2^(j+3)-d ∧ x (v-(a : ℤ)) a = true ∧
          x (v-(a : ℤ)) (a+d) = true) →
      ∀ p : ℤ, (∀ b < 2^(j+3), x p b =
        (decide (b < 2^j) || (decide (3*2^j ≤ b) && decide (b < 5*2^j)) || decide (7*2^j ≤ b))) →
      ∀ r : ℤ, p - 7*2^j ≤ r → r ≤ p + 7*2^j →
        ((r - p) % 2 = 0 → x r 1 = true ∧ ∀ i < 2^(j+2), x r (2*i) = x r (2*i+1)) ∧
        ((r - p) % 2 = 1 → ∀ a, 0 < a → a < 2^(j+3) - 1 → x r a = false))
    (hCTr : ∀ t : ℕ, 3 ≤ t → ∀ (x : ℤ → ℕ → Bool),
      (∀ p, cycle_power_dyadic_class_weight (t+1) (x p) =
        (Finset.range (2^(t+1))).sum (fun a => (x p a).toNat)) →
      (∀ i < t+1, ∀ v : ℤ, (Finset.range (2^i)).sum (fun a =>
        (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^(t+1)-2^i)).toNat) = 1) →
      (∀ d : ℕ, 1 ≤ d → d < 2^(t+1) → ∀ v : ℤ,
        ∃ a : ℕ, a < 2^(t+1)-d ∧ x (v-(a : ℤ)) a = true ∧
          x (v-(a : ℤ)) (a+d) = true) →
      (∀ v : ℤ, (Finset.range (2^(t+1))).sum (fun a =>
        (x (v-(a : ℤ)) a).toNat) = (t+1)+1) →
      ∀ p0 : ℤ,
      (∀ r : ℤ, p0 - 3*2^t ≤ r → r ≤ p0 →
        ((p0 - r) % 2 = 0 → x r 1 = true ∧ ∀ i < 2^t, x r (2*i) = x r (2*i+1)) ∧
        ((p0 - r) % 2 = 1 → ∀ a, 0 < a → a < 2^(t+1) - 1 → x r a = false)) →
      (∀ a, 0 < a → a < 2^(t+1) - 1 → x (p0+1) a = false) ∧
      (x (p0+2) 1 = true ∧ ∀ i < 2^t, x (p0+2) (2*i) = x (p0+2) (2*i+1)))
    (k m n : ℕ) (hm : 1 ≤ m) (hkm : k + 1 = 2 ^ m)
    (hn : max (2 * k + 2) (k ^ 2 * (k + 2)) ≤ n) (hev : Even n) (hnd : ¬ (k + 1) ∣ n) :
    simple_graph_equivalence_covering_number (simple_graph_cycle_power n k) = m + 2 := by
  refine simple_graph_equivalence_covering_number_cycle_power_two_pow_even_not_dvd_of_regular_continuation
    hfull hIR hCTr ?_ k m n hm hkm hn hev hnd
  intro t ht x htight hexact hcover hcount p0 hreg
  exact cycle_power_dyadic_regular_continuation_left_of_right t (hCTr t ht) x htight hexact hcover
    hcount p0 hreg
