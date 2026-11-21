import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphEquivalenceCoveringNumber
import AFTD.Kb.Tcs.SimpleGraphCyclePower
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.SimpleGraphEquivalenceCoveringNumberCyclePowerDyadicOfClassShape
import AFTD.Kb.Tcs.CyclePowerDyadicFoldStructStep
import AFTD.Kb.Tcs.CyclePowerFifteenModelAlternatingEndpoint
import AFTD.Kb.Tcs.CyclePowerThirtyOneMiddleBitsOfAlternating
import AFTD.Kb.Tcs.CyclePowerDyadicNoIslandOfAlternatingEndpoint
import AFTD.Kb.Tcs.CyclePowerFifteenModelNoIsland

/-!
# simple_graph_equivalence_covering_number_cycle_power_thirty_one_of_left_count_periodic

Topic: combinatorics   Node: 16a306f2c715

Provenance: helper lemma. RT-1 / OP-205, arXiv:2610.15635: the k = 31 (m = 5) case of the open even case, conditional on the exponent-5 left-count periodicity.

Conditional k = 31 case of OP-205: if every tight, exactly dyadically covered, fully covered exponent-5 model with 6 active classes per vertex has 16-periodic left count, then for every even n >= 31713 = 31^2 * 33 not divisible by 32, the equivalence covering number of the 31st power of the n-cycle is 7.
-/

theorem simple_graph_equivalence_covering_number_cycle_power_thirty_one_of_left_count_periodic
    (hfold : ∀ (x : ℤ → ℕ → Bool),
      (∀ p, cycle_power_dyadic_class_weight (4+1) (x p) =
        (Finset.range (2^(4+1))).sum (fun a => (x p a).toNat)) →
      (∀ j < 4+1, ∀ v : ℤ, (Finset.range (2^j)).sum (fun a =>
        (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^(4+1)-2^j)).toNat) = 1) →
      (∀ d : ℕ, 1 ≤ d → d < 2^(4+1) → ∀ v : ℤ,
        ∃ a : ℕ, a < 2^(4+1)-d ∧ x (v-(a : ℤ)) a = true ∧
          x (v-(a : ℤ)) (a+d) = true) →
      (∀ v : ℤ, (Finset.range (2^(4+1))).sum (fun a =>
        (x (v-(a : ℤ)) a).toNat) = (4+1)+1) →
      ∀ v : ℤ, (Finset.range (2^4)).sum (fun a => (x (v-(a : ℤ)) a).toNat) =
        (Finset.range (2^4)).sum (fun a => (x (v+(2:ℤ)^4-(a : ℤ)) a).toNat))
    (n : ℕ) (hn : 31713 ≤ n) (hev : Even n) (hnd : ¬ 32 ∣ n) :
    simple_graph_equivalence_covering_number (simple_graph_cycle_power n 31) = 7 := by
  refine simple_graph_equivalence_covering_number_cycle_power_dyadic_of_class_shape 31 5 n
    (by norm_num) (by norm_num) (by norm_num; omega) hev (by simpa using hnd) ?_
  intro y htight hexact hcover hcount
  obtain ⟨halt, hend⟩ := cycle_power_dyadic_fold_struct_step 4 (by norm_num)
    cycle_power_fifteen_model_alternating_endpoint y htight hexact hcover hcount
    (hfold y htight hexact hcover hcount)
    (cycle_power_thirty_one_middle_bits_of_alternating y htight hexact hcover hcount)
  exact cycle_power_dyadic_no_island_of_alternating_endpoint 4 (by norm_num)
    cycle_power_fifteen_model_no_island y htight hexact hcover hcount halt hend
