import AFTD.Prelude
import AFTD.Kb.Tcs.MinGaleCounterexampleCardThree
import AFTD.Kb.Tcs.IsGaleCounterexampleThree

/-!
# op_462_is_least_iff

Topic: combinatorics   Node: e3a17eec0225

Provenance: original. Related work: folklore

For every natural number m, m is the least element of the set of cardinalities of finite counterexamples to Gale's conjecture in dimension 3 if and only if there exists a finite counterexample of cardinality m and min_gale_counterexample_card_three is equal to m.
-/

/-- A natural number m is the least cardinality of a counterexample to Gale's conjecture in dimension 3 iff an m-point counterexample exists and min_gale_counterexample_card_three = m. -/
theorem op_462_is_least_iff (m : ℕ) :
    IsLeast {k : ℕ | ∃ V : Finset (EuclideanSpace ℝ (Fin 3)), V.card = k ∧ is_gale_counterexample_three V} m ↔
    (∃ V : Finset (EuclideanSpace ℝ (Fin 3)), V.card = m ∧ is_gale_counterexample_three V) ∧
    min_gale_counterexample_card_three = m := by
  constructor
  · intro h
    refine ⟨h.1, ?_⟩
    unfold min_gale_counterexample_card_three
    have hne : ({k : ℕ | ∃ V : Finset (EuclideanSpace ℝ (Fin 3)), V.card = k ∧ is_gale_counterexample_three V}).Nonempty := ⟨m, h.1⟩
    refine le_antisymm (Nat.sInf_le h.1) ?_
    exact @h.2 (sInf {k : ℕ | ∃ V : Finset (EuclideanSpace ℝ (Fin 3)), V.card = k ∧ is_gale_counterexample_three V}) (Nat.sInf_mem hne)
  · intro ⟨hm, hmin⟩
    refine ⟨hm, ?_⟩
    intro b hb
    rw [show m = min_gale_counterexample_card_three from hmin.symm]
    exact Nat.sInf_le hb
