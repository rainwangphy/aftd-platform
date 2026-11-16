import AFTD.Prelude
import AFTD.Kb.Tcs.Op1370BooleanIntervalCancellation

/-!
# op1370_uniform_hull_weighted_entry

Topic: combinatorics   Node: 75c1c64c0b72

Provenance: helper lemma.

Uniform weights on the interval hull of any finite set family produce a scalar identity in the signed weighted-incidence matrix.
-/

open Finset Matrix Polynomial
open scoped BigOperators

theorem op1370_uniform_hull_weighted_entry
    {α V K : Type*} [DecidableEq α] [Fintype α] [Fintype V] [DecidableEq V] [Field K]
    (A : V → Finset α) (hA : Function.Injective A) (q : Finset α → K) (u : K)
    (hq : ∀ X, (∃ a b, A a ⊆ X ∧ X ⊆ A b) → q X = u) (a b : V) :
    (∑ X : Finset α, q X *
      ((if A a ⊆ X then (-1 : K) ^ (X \ A a).card else 0) *
        (if X ⊆ A b then 1 else 0))) = u * (if a = b then 1 else 0) := by
  classical
  let g (X : Finset α) : K := q X *
    ((if A a ⊆ X then (-1 : K) ^ (X \ A a).card else 0) *
      (if X ⊆ A b then 1 else 0))
  change (∑ X : Finset α, g X) = _
  by_cases hAB : A a ⊆ A b
  · have hr : (∑ X : Finset α, g X) = ∑ X ∈ Finset.Icc (A a) (A b), g X := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro X _ hX
      by_cases h1 : A a ⊆ X
      · have h2 : ¬ X ⊆ A b := by
          intro h2
          exact hX (Finset.mem_Icc.mpr ⟨h1, h2⟩)
        simp [g, h2]
      · simp [g, h1]
    have hc : (∑ X ∈ Finset.Icc (A a) (A b), (-1 : K) ^ (X \ A a).card) =
        if A a = A b then 1 else 0 := by
      have hh := congrArg (Int.castRingHom K)
        (op1370_boolean_interval_cancellation (A a) (A b) hAB)
      simpa only [map_sum, map_pow, map_neg, map_one, map_zero, apply_ite] using hh
    calc
      (∑ X : Finset α, g X) = ∑ X ∈ Finset.Icc (A a) (A b), g X := hr
      _ = u * ∑ X ∈ Finset.Icc (A a) (A b), (-1 : K) ^ (X \ A a).card := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro X hX
        obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hX
        have hqX := hq X ⟨a, b, h1, h2⟩
        simp [g, h1, h2, hqX]
      _ = u * (if A a = A b then 1 else 0) := by rw [hc]
      _ = u * (if a = b then 1 else 0) := by
        by_cases hab : a = b
        · subst b
          simp
        · have hne : A a ≠ A b := fun h => hab (hA h)
          simp [hab, hne]
  · have hab : a ≠ b := by
      intro h
      subst b
      exact hAB Finset.Subset.rfl
    simp only [hab, ↓reduceIte, mul_zero]
    apply Finset.sum_eq_zero
    intro X _
    by_cases h1 : A a ⊆ X
    · have h2 : ¬ X ⊆ A b := fun h2 => hAB (h1.trans h2)
      simp [g, h2]
    · simp [g, h1]
