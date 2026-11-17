import AFTD.Prelude
import AFTD.Kb.Tcs.Op869ExtendPredecessors

/-!
# op869_extend_predecessors_update

Topic: online_algorithms   Node: 5b89499389c0

Provenance: helper lemma. Padding and monotonicity for the finite adversary game of arXiv:2610.41516 Section 2.

Padding a predecessor-set update agrees with updating the padded presentation.
-/

/-- Padding a predecessor-set update agrees with updating the padded presentation. -/
theorem op869_extend_predecessors_update {n m : ℕ} (h : n ≤ m) (P : Fin n → Finset (Fin n))
    (i : Fin n) (S : Finset (Fin n)) :
    op869_extend_predecessors h (Function.update P i S) =
      Function.update (op869_extend_predecessors h P) (Fin.castLE h i) (S.map (Fin.castLEEmb h)) := by
  classical
  funext v
  by_cases hvi : v = Fin.castLE h i
  · subst v
    simp [op869_extend_predecessors, i.isLt]
  · by_cases hv : v.val < n
    · have hbne : (⟨v.val, hv⟩ : Fin n) ≠ i := by
        intro heq
        apply hvi
        apply Fin.ext
        exact congrArg (fun z : Fin n => z.val) heq
      simp [op869_extend_predecessors, hv, Function.update_of_ne, hvi, hbne]
    · simp [op869_extend_predecessors, hv, Function.update_of_ne, hvi]
