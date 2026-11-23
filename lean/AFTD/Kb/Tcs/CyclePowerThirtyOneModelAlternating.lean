import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight
import AFTD.Kb.Tcs.CyclePowerThirtyOneModelBitOneNotBothFalse
import AFTD.Kb.Tcs.CyclePowerThirtyOneModelBitOneNotBothTrue

/-!
# cycle_power_thirty_one_model_alternating

Topic: combinatorics   Node: ba21144d52cb

Provenance: helper lemma. RT-1 / OP-205, arXiv:2610.15635: the k = 31 (m = 5) case of the open even case. The one remaining hypothesis of simple_graph_equivalence_covering_number_cycle_power_thirty_one_of_alternating; window SAT evidence experiment 37427.

In a tight, exactly dyadically covered, fully covered exponent-5 Boolean class model with 6 active classes at every vertex, bit 1 alternates: x(p+1,1) = not x(p,1) for every p.
-/

theorem cycle_power_thirty_one_model_alternating (x : ℤ → ℕ → Bool)
    (htight : ∀ p, cycle_power_dyadic_class_weight (4+1) (x p) =
        (Finset.range (2^(4+1))).sum (fun a => (x p a).toNat))
    (hexact : ∀ j < 4+1, ∀ v : ℤ, (Finset.range (2^j)).sum (fun a =>
        (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+2^(4+1)-2^j)).toNat) = 1)
    (hcover : ∀ d : ℕ, 1 ≤ d → d < 2^(4+1) → ∀ v : ℤ,
        ∃ a : ℕ, a < 2^(4+1)-d ∧ x (v-(a : ℤ)) a = true ∧
          x (v-(a : ℤ)) (a+d) = true)
    (hcount : ∀ v : ℤ, (Finset.range (2^(4+1))).sum (fun a =>
        (x (v-(a : ℤ)) a).toNat) = (4+1)+1) :
    ∀ p : ℤ, x (p+1) 1 = !x p 1 := by
  intro p
  cases h : x p 1
  · simpa using cycle_power_thirty_one_model_bit_one_not_both_false x htight hexact hcover hcount p h
  · simpa using cycle_power_thirty_one_model_bit_one_not_both_true x htight hexact hcover hcount p h
