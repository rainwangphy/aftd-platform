import AFTD.Prelude
import AFTD.Kb.Tcs.ApplyCliffordGate
import AFTD.Kb.Tcs.PauliSize
import AFTD.Kb.Tcs.CliffordGate
import AFTD.Kb.Tcs.PauliLabel

/-!
# pauli_size_apply_clifford_gate_cnot_le

Topic: quantum   Node: 3960d3b201f9

Provenance: helper lemma. step towards op_757_all_to_all_cnot_lower_bound

Applying a CNOT gate increases the Pauli size by at most 1.
-/

/-- Applying a CNOT gate increases the Pauli size by at most 1. -/
theorem pauli_size_apply_clifford_gate_cnot_le {k : ℕ} (c t : Fin k) (hct : c ≠ t) (p : PauliLabel k) :
    pauli_size (apply_clifford_gate (.cnot c t hct) p) ≤ pauli_size p + 1 := by
  classical
  set A : Finset (Fin k) := Finset.univ.filter (fun i => p.1 i ≠ 0 ∨ p.2 i ≠ 0) with hA
  have hsize : pauli_size p = A.card := by rw [pauli_size, ← hA]
  have hmem : ∀ i : Fin k, (i ∈ A ↔ (p.1 i ≠ 0 ∨ p.2 i ≠ 0)) := by
    intro i; rw [hA]; simp
  set q := apply_clifford_gate (CliffordGate.cnot c t hct) p with hq
  have hq1 : q.1 = Function.update p.1 t (p.1 t + p.1 c) := by rw [hq]; rfl
  have hq2 : q.2 = Function.update p.2 c (p.2 c + p.2 t) := by rw [hq]; rfl
  have hqsize : pauli_size q = (Finset.univ.filter (fun i : Fin k => q.1 i ≠ 0 ∨ q.2 i ≠ 0)).card := rfl
  by_cases ht : t ∈ A
  · have hsub : Finset.univ.filter (fun i : Fin k => q.1 i ≠ 0 ∨ q.2 i ≠ 0) ⊆ insert c A := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rw [Finset.mem_insert]
      by_cases hic : i = c
      · exact Or.inl hic
      · right
        by_cases hit : i = t
        · rw [hit]; exact ht
        · have e1 : q.1 i = p.1 i := by rw [hq1, Function.update_of_ne hit]
          have e2 : q.2 i = p.2 i := by rw [hq2, Function.update_of_ne hic]
          rw [e1, e2] at hi
          exact (hmem i).mpr hi
    calc pauli_size q = (Finset.univ.filter (fun i : Fin k => q.1 i ≠ 0 ∨ q.2 i ≠ 0)).card := hqsize
      _ ≤ (insert c A).card := Finset.card_le_card hsub
      _ ≤ A.card + 1 := Finset.card_insert_le c A
      _ = pauli_size p + 1 := by rw [hsize]
  · have ht1 : p.1 t = 0 := by
      by_contra h
      exact ht ((hmem t).mpr (Or.inl h))
    have ht2 : p.2 t = 0 := by
      by_contra h
      exact ht ((hmem t).mpr (Or.inr h))
    have hsub : Finset.univ.filter (fun i : Fin k => q.1 i ≠ 0 ∨ q.2 i ≠ 0) ⊆ insert t A := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
      rw [Finset.mem_insert]
      by_cases hit : i = t
      · exact Or.inl hit
      · right
        by_cases hic : i = c
        · rw [hic] at hi ⊢
          have e1 : q.1 c = p.1 c := by rw [hq1, Function.update_of_ne hct]
          have e2 : q.2 c = p.2 c := by rw [hq2]; simp [ht2]
          rw [e1, e2] at hi
          exact (hmem c).mpr hi
        · have e1 : q.1 i = p.1 i := by rw [hq1, Function.update_of_ne hit]
          have e2 : q.2 i = p.2 i := by rw [hq2, Function.update_of_ne hic]
          rw [e1, e2] at hi
          exact (hmem i).mpr hi
    calc pauli_size q = (Finset.univ.filter (fun i : Fin k => q.1 i ≠ 0 ∨ q.2 i ≠ 0)).card := hqsize
      _ ≤ (insert t A).card := Finset.card_le_card hsub
      _ ≤ A.card + 1 := Finset.card_insert_le t A
      _ = pauli_size p + 1 := by rw [hsize]
