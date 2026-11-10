import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight

/-!
# cycle_power_dyadic_defective_half_model

Topic: combinatorics   Node: 0a1723d9b22f

Provenance: helper lemma. Defective half-model bookkeeping for research thread RT-1; two parity phases are distinguished explicitly.

A dyadic half model with a Boolean defect: lower ranks have unique owners, top-rank ownership and the active count each lose one at a defect, with an explicit phase shift; every other distance is covered.
-/

def cycle_power_dyadic_defective_half_model (t : ℕ) (y : ℤ → ℕ → Bool) (e : ℤ → Bool) (shift : ℤ) : Prop := (∀ p, cycle_power_dyadic_class_weight t (y p) = (Finset.range (2^t)).sum (fun a => (y p a).toNat)) ∧
    (∀ j, j + 1 < t → ∀ v : ℤ, (Finset.range (2^j)).sum (fun a =>
      (y (v-(a : ℤ)) a && y (v-(a : ℤ)) (a+2^t-2^j)).toNat) = 1) ∧
    (∀ v : ℤ, (Finset.range (2^(t-1))).sum (fun a =>
      (y (v-(a : ℤ)) a && y (v-(a : ℤ)) (a+2^t-2^(t-1))).toNat) + (e (v+shift)).toNat = 1) ∧
    (∀ d : ℕ, 1 ≤ d → d < 2^t → d ≠ 2^(t-1) → ∀ v : ℤ,
      ∃ a : ℕ, a < 2^t-d ∧ y (v-(a : ℤ)) a = true ∧ y (v-(a : ℤ)) (a+d) = true) ∧
    (∀ v : ℤ, (Finset.range (2^t)).sum (fun a => (y (v-(a : ℤ)) a).toNat) + (e v).toNat = t+1)
