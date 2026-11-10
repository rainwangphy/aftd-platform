import AFTD.Prelude
import AFTD.Kb.NumberTheory.IsCompleteSequence

/-!
# is_complete_sequence_const_one

Topic: elementary_number_theory   Node: 311bc175a97b

Provenance: helper lemma. folklore

The sequence defined by H(n) = 1 for all n ≥ 1 and H(0) = 0 is a complete sequence.
-/

/-- The sequence constant 1 for n ≥ 1 is a complete sequence. -/
theorem is_complete_sequence_const_one :
    is_complete_sequence (fun n => if 1 ≤ n then 1 else 0) := by
  intro t ht
  refine ⟨Finset.Icc 1 t.toNat, ?_, ?_⟩
  · intro i hi
    exact (Finset.mem_Icc.mp hi).1
  · have htn : (t.toNat : ℤ) = t := Int.toNat_of_nonneg (by omega)
    have h1 : ∀ i ∈ Finset.Icc 1 t.toNat, (if 1 ≤ i then (1:ℤ) else 0) = 1 := by
      intro i hi
      simp [(Finset.mem_Icc.mp hi).1]
    rw [Finset.sum_congr rfl h1]
    simp [htn]
