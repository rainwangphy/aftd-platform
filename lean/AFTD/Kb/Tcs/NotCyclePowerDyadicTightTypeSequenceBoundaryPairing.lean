import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerDyadicClassWeight

/-!
# not_cycle_power_dyadic_tight_type_sequence_boundary_pairing

Topic: combinatorics   Node: b8d5a6c15f30

Provenance: original. Related work: Refutes the auxiliary statement proposed during IN-215 for OP-205, arXiv:2610.15635. Countermodel verified in experiment5761. This does not refute the graph-cover conjecture.

The proposed uniform layer-free boundary-pairing statement allowing m=2 is false: every class can have the constant type {0,1,3}. This auxiliary model is not a three-layer equivalence cover.
-/

theorem not_cycle_power_dyadic_tight_type_sequence_boundary_pairing : ¬ (∀ (m : ℕ) (hm : 2 ≤ m) (x : ℤ → ℕ → Bool)
    (h0 : ∀ p, x p 0 = true) (hend : ∀ p, x p (2 ^ m - 1) = true)
    (hweight : ∀ p, cycle_power_dyadic_class_weight m (x p) =
      (Finset.range (2 ^ m)).sum (fun j => (x p j).toNat))
    (hcount : ∀ v : ℤ, (Finset.range (2 ^ m)).sum
      (fun j => (x (v - (j : ℤ)) j).toNat) = m + 1)
    (hexact : ∀ (j : ℕ), j < m → ∀ v : ℤ,
      (Finset.range (2 ^ j)).sum (fun a =>
        (x (v - (a : ℤ)) a && x (v - (a : ℤ)) (a + 2 ^ m - 2 ^ j)).toNat) = 1)
    (hcover : ∀ (d : ℕ), 1 ≤ d → d < 2 ^ m → ∀ v : ℤ,
      ∃ a < 2 ^ m - d, x (v - (a : ℤ)) a = true ∧
        x (v - (a : ℤ)) (a + d) = true), ∀ p, x p 1 = x p (2 ^ m - 2)) := by
  intro h
  let x : ℤ → ℕ → Bool := fun _ j => decide (j = 0 ∨ j = 1 ∨ j = 3)
  have h0 : ∀ p, x p 0 = true := by intro p; rfl
  have hend : ∀ p, x p (2 ^ 2 - 1) = true := by intro p; rfl
  have hw : ∀ p, cycle_power_dyadic_class_weight 2 (x p) =
      (Finset.range (2 ^ 2)).sum (fun j => (x p j).toNat) := by
    intro p
    norm_num [cycle_power_dyadic_class_weight, x, Finset.sum_range_succ]
  have hc : ∀ v : ℤ, (Finset.range (2 ^ 2)).sum
      (fun j => (x (v - (j : ℤ)) j).toNat) = 2 + 1 := by
    intro v
    norm_num [x, Finset.sum_range_succ]
  have hexc : ∀ (j : ℕ), j < 2 → ∀ v : ℤ,
      (Finset.range (2 ^ j)).sum (fun a =>
        (x (v - (a : ℤ)) a && x (v - (a : ℤ)) (a + 2 ^ 2 - 2 ^ j)).toNat) = 1 := by
    intro j hj v
    interval_cases j <;> norm_num [x, Finset.sum_range_succ]
  have hcov : ∀ (d : ℕ), 1 ≤ d → d < 2 ^ 2 → ∀ v : ℤ,
      ∃ a < 2 ^ 2 - d, x (v - (a : ℤ)) a = true ∧
        x (v - (a : ℤ)) (a + d) = true := by
    intro d hd hd4 v
    norm_num at hd4
    interval_cases d
    · exact ⟨0, by decide, by norm_num [x], by norm_num [x]⟩
    · exact ⟨1, by decide, by norm_num [x], by norm_num [x]⟩
    · exact ⟨0, by decide, by norm_num [x], by norm_num [x]⟩
  have he := h 2 (by omega) x h0 hend hw hc hexc hcov 0
  norm_num [x] at he
