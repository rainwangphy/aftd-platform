import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerThirtyOneModelAlternating
import AFTD.Kb.Tcs.CyclePowerThirtyOneEndpointBitsOfAlternating
import AFTD.Kb.Tcs.CyclePowerThirtyOneMiddleBitsOfAlternating
import AFTD.Kb.Tcs.CyclePowerDyadicNoIslandOfAlternatingEndpoint
import AFTD.Kb.Tcs.CyclePowerFifteenModelNoIsland
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight

/-!
# cycle_power_thirty_one_model_no_island

Topic: combinatorics   Node: bbeb1bdfc7d5

Provenance: helper lemma. Helper step for the main statement of OP-205 (arXiv:2610.15635, the case k+1 = 2^m, n even, (k+1) not dividing n, left open there); it concerns the integer Boolean class models that optimal (m+1)-layer covers give. Exponent-5 instance of the no-island property, assembled from the proved alternation, endpoint-bit and middle-bit lemmas at exponent 5.

In a tight, exactly dyadically covered, fully covered integer Boolean class model at exponent 5 (classes of span 32) with exactly 6 active classes at every vertex, no class has a selected offset strictly between a missing offset and a later missing offset: every class is the union of an initial and a terminal interval.
-/

theorem cycle_power_thirty_one_model_no_island (x : ℤ → ℕ → Bool)
    (htight : ∀ p, cycle_power_dyadic_class_weight 5 (x p) =
      (Finset.range (2^5)).sum (fun a => (x p a).toNat))
    (hexact : ∀ j < 5, ∀ v : ℤ, (Finset.range (2^j)).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^5-2^j)).toNat) = 1)
    (hcover : ∀ d : ℕ, 1 ≤ d → d < 2^5 → ∀ v : ℤ,
      ∃ a : ℕ, a < 2^5-d ∧ x (v-(a : ℤ)) a = true ∧
        x (v-(a : ℤ)) (a+d) = true)
    (hcount : ∀ v : ℤ, (Finset.range (2^5)).sum (fun a =>
      (x (v-(a : ℤ)) a).toNat) = 5+1) :
    ∀ (p : ℤ) (a b c : ℕ), a < b → b < c → c < 2^5 →
      x p a = false → x p b = true → x p c = true := by
  have halt := cycle_power_thirty_one_model_alternating x htight hexact hcover hcount
  have hpart := cycle_power_thirty_one_endpoint_bits_of_alternating x htight hexact hcover halt
  have hmid := cycle_power_thirty_one_middle_bits_of_alternating x htight hexact hcover hcount
    halt hpart
  have hend : ∀ p : ℤ, x p 1 = false → ∀ j, 0 < j → j < 2^(4+1) - 1 → x p j = false := by
    intro p hp j hj0 hj1
    by_cases h15 : j = 2^4 - 1
    · rw [h15]; exact (hmid p hp).1
    by_cases h16 : j = 2^4
    · rw [h16]; exact (hmid p hp).2
    exact hpart p hp j hj0 hj1 h15 h16
  exact cycle_power_dyadic_no_island_of_alternating_endpoint 4 (by norm_num)
    cycle_power_fifteen_model_no_island x htight hexact hcover hcount halt hend
