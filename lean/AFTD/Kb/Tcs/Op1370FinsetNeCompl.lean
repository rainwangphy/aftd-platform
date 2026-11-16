import AFTD.Prelude

/-!
# op1370_finset_ne_compl

Topic: combinatorics   Node: 1234d32fd13d

Provenance: helper lemma.

No subset of a nonempty finite set equals its complement.
-/

open Finset Matrix Polynomial
open scoped BigOperators

theorem op1370_finset_ne_compl
    {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α] (Y : Finset α) : Y ≠ Yᶜ := by
  intro h
  let x : α := Classical.choice ‹Nonempty α›
  have hx : x ∈ Y ↔ x ∉ Y := by
    have hh := congrArg (fun T : Finset α => x ∈ T) h
    simpa using hh
  by_cases hy : x ∈ Y
  · exact (hx.mp hy) hy
  · exact hy (hx.mpr hy)
