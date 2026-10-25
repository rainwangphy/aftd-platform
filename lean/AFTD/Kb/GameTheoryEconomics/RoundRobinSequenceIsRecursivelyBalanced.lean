import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsRecursivelyBalanced
import AFTD.Kb.GameTheoryEconomics.RoundRobinSequence

/-!
# round_robin_sequence_is_recursively_balanced

Topic: fair_division   Node: f6227b94e219

Provenance: formalization of a published result. Source: arXiv:2610.23686, Sec. 2

Every Round-Robin picking sequence of length m for n agents is recursively balanced.
-/

/-- Every Round-Robin picking sequence is recursively balanced. -/
theorem round_robin_sequence_is_recursively_balanced (n m : ℕ) [NeZero n] :
    is_recursively_balanced n (round_robin_sequence n m) := by
  intro s
  rw [List.nodup_iff_injective_getElem]
  rintro ⟨i, hi⟩ ⟨j, hj⟩ (hij : _ = _)
  dsimp at hij
  have hlen_i : s * n + i < (round_robin_sequence n m).length ∧ i < n := by
    rw [List.length_take, List.length_drop] at hi
    omega
  have hlen_j : s * n + j < (round_robin_sequence n m).length ∧ j < n := by
    rw [List.length_take, List.length_drop] at hj
    omega
  have hi_eq : (((round_robin_sequence n m).drop (s * n)).take n)[i] = (round_robin_sequence n m)[s * n + i] := by
    rw [List.getElem_take, List.getElem_drop]
  have hj_eq : (((round_robin_sequence n m).drop (s * n)).take n)[j] = (round_robin_sequence n m)[s * n + j] := by
    rw [List.getElem_take, List.getElem_drop]
  rw [hi_eq, hj_eq] at hij
  unfold round_robin_sequence at hij
  simp only [List.getElem_ofFn] at hij
  have hval : (s * n + i) % n = (s * n + j) % n := by
    exact Fin.ext_iff.mp hij
  have hmod_i : (s * n + i) % n = i := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlen_i.2]
  have hmod_j : (s * n + j) % n = j := by
    rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hlen_j.2]
  rw [hmod_i, hmod_j] at hval
  exact Fin.ext hval
