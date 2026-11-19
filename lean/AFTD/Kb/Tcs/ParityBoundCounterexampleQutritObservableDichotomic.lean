import AFTD.Prelude
import AFTD.Kb.Tcs.ParityBoundCounterexampleQutritObservable
import AFTD.Kb.Tcs.IsDichotomicProjectiveObservable

/-!
# parity_bound_counterexample_qutrit_observable_dichotomic

Topic: quantum   Node: 720b7d18e66d

Provenance: helper lemma. step towards open_problem_735_parity_bound_higher_dimension

Every matrix of the qutrit counterexample family — diag(1,-1,1) and the identity on ℂ^3 — is a dichotomic projective observable: Hermitian and squaring to the identity.
-/

/-- Both qutrit counterexample matrices are Hermitian and square to the identity, hence dichotomic projective observables on ℂ³. -/
theorem parity_bound_counterexample_qutrit_observable_dichotomic : ∀ y : Fin 2, is_dichotomic_projective_observable (parity_bound_counterexample_qutrit_observable y) := by
  intro y
  fin_cases y
  · dsimp [parity_bound_counterexample_qutrit_observable]
    unfold is_dichotomic_projective_observable
    constructor
    · rw [Matrix.isHermitian_diagonal_iff]
      intro i
      split_ifs <;> simp [IsSelfAdjoint]
    · rw [Matrix.diagonal_mul_diagonal]
      have : (fun i : Fin 3 => (if i = 1 then (-1 : ℂ) else 1) * if i = 1 then -1 else 1) = fun _ => 1 := by
        ext i
        split_ifs <;> ring
      rw [this]
      exact Matrix.diagonal_one
  · dsimp [parity_bound_counterexample_qutrit_observable]
    unfold is_dichotomic_projective_observable
    exact ⟨Matrix.isHermitian_one, mul_one 1⟩
