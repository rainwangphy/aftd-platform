import AFTD.Prelude

/-!
# cycle_power_exact_pair_exists

Topic: combinatorics   Node: d82c4d330d3c

Provenance: helper lemma. Uniform full-root-gap and current-scale fullness reduction for OP-205 / RT-1 following arXiv:2610.15635. The reusable finite ordered-cover classification formalizes the deficiency-one structure described in arXiv:1103.3693 Corollary 2.5.6. Explicit full-class or middle-fullness hypotheses remain structural assumptions where used; optimal original counts have not been shown to imply them. No graph covering value or research advance is claimed.

An exact Boolean pair-count sum of one supplies a selected owning pair.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem cycle_power_exact_pair_exists
    (D R : ℕ) (x : ℤ → ℕ → Bool)
    (hexact : ∀ v : ℤ, (range R).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+D-R)).toNat) = 1) :
    ∀ v : ℤ, ∃ a : ℕ, a < R ∧ x (v-(a : ℤ)) a = true ∧ x (v-(a : ℤ)) (a+D-R) = true := by
  intro v
  obtain ⟨a, ha, he⟩ := exists_ne_zero_of_sum_ne_zero
    (show (range R).sum (fun a =>
      (x (v-(a : ℤ)) a && x (v-(a : ℤ)) (a+D-R)).toNat) ≠ 0 by rw [hexact v]; decide)
  refine ⟨a, mem_range.mp ha, ?_⟩
  cases h₀ : x (v-(a : ℤ)) a <;> cases h₁ : x (v-(a : ℤ)) (a+D-R) <;>
    simp_all only [Bool.false_and, Bool.true_and, Bool.toNat_false, Bool.toNat_true,
      ne_eq, not_true_eq_false, and_self]
