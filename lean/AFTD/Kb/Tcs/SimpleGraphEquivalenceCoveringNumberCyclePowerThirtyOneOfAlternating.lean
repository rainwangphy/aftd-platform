import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphEquivalenceCoveringNumber
import AFTD.Kb.Tcs.SimpleGraphCyclePower
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.SimpleGraphEquivalenceCoveringNumberCyclePowerDyadicOfClassShape
import AFTD.Kb.Tcs.CyclePowerThirtyOneEndpointBitsOfAlternating
import AFTD.Kb.Tcs.CyclePowerThirtyOneMiddleBitsOfAlternating
import AFTD.Kb.Tcs.CyclePowerDyadicNoIslandOfAlternatingEndpoint
import AFTD.Kb.Tcs.CyclePowerFifteenModelNoIsland

/-!
# simple_graph_equivalence_covering_number_cycle_power_thirty_one_of_alternating

Topic: combinatorics   Node: 3939eabaa417

Provenance: helper lemma. RT-1 / OP-205, arXiv:2610.15635: the k = 31 (m = 5) case of the open even case. Conditional on alternation of bit 1 in exponent-5 models; replaces the left-count hypothesis of simple_graph_equivalence_covering_number_cycle_power_thirty_one_of_left_count_periodic by a local one.

Conditional k = 31 case of OP-205: if bit 1 alternates (x(p+1,1) = not x(p,1)) in every tight, exactly dyadically covered, fully covered exponent-5 model with 6 active classes per vertex, then for every even n >= 31713 not divisible by 32 the equivalence covering number of the 31st power of the n-cycle is 7.
-/

theorem simple_graph_equivalence_covering_number_cycle_power_thirty_one_of_alternating
    (halt5 : ∀ (x : ℤ → ℕ → Bool),
      (∀ p, cycle_power_dyadic_class_weight (4+1) (x p) =
        (Finset.range (2^(4+1))).sum (fun a => (x p a).toNat)) →
      (∀ j < 4+1, ∀ v : ℤ, (Finset.range (2^j)).sum (fun a =>
        (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^(4+1)-2^j)).toNat) = 1) →
      (∀ d : ℕ, 1 ≤ d → d < 2^(4+1) → ∀ v : ℤ,
        ∃ a : ℕ, a < 2^(4+1)-d ∧ x (v-(a : ℤ)) a = true ∧
          x (v-(a : ℤ)) (a+d) = true) →
      (∀ v : ℤ, (Finset.range (2^(4+1))).sum (fun a =>
        (x (v-(a : ℤ)) a).toNat) = (4+1)+1) →
      ∀ p : ℤ, x (p+1) 1 = !x p 1)
    (n : ℕ) (hn : 31713 ≤ n) (hev : Even n) (hnd : ¬ 32 ∣ n) :
    simple_graph_equivalence_covering_number (simple_graph_cycle_power n 31) = 7 := by
  refine simple_graph_equivalence_covering_number_cycle_power_dyadic_of_class_shape 31 5 n
    (by norm_num) (by norm_num) (by norm_num; omega) hev (by simpa using hnd) ?_
  intro y htight hexact hcover hcount
  have halt := halt5 y htight hexact hcover hcount
  have hpart := cycle_power_thirty_one_endpoint_bits_of_alternating y htight hexact hcover halt
  have hmid := cycle_power_thirty_one_middle_bits_of_alternating y htight hexact hcover hcount
    halt hpart
  have hend : ∀ p : ℤ, y p 1 = false → ∀ j, 0 < j → j < 2^(4+1) - 1 → y p j = false := by
    intro p hp j hj0 hj1
    by_cases h15 : j = 2^4 - 1
    · rw [h15]; exact (hmid p hp).1
    by_cases h16 : j = 2^4
    · rw [h16]; exact (hmid p hp).2
    exact hpart p hp j hj0 hj1 h15 h16
  exact cycle_power_dyadic_no_island_of_alternating_endpoint 4 (by norm_num)
    cycle_power_fifteen_model_no_island y htight hexact hcover hcount halt hend
