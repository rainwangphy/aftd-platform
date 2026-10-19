import AFTD.Prelude
import AFTD.Kb.NumberTheory.IntBoxThree

/-!
# int_box_three_mem_iff

Topic: elementary_number_theory   Node: 4c5b8102184e

Provenance: helper lemma. Sanity lemma for int_box_three.

A vector lies in [[-m,m]]^3 iff each coordinate has absolute value at most m.
-/

theorem int_box_three_mem_iff (m : ℕ) (v : Fin 3 → ℤ) :
    v ∈ int_box_three m ↔ ∀ i, |v i| ≤ m := by
  simp only [int_box_three, Set.mem_setOf_eq, abs_le]
