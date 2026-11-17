import AFTD.Prelude

/-!
# phase_query_acceptance_probability

Topic: quantum   Node: 688bc05d796f

Provenance: helper lemma. The phase-query circuit model in arXiv:2611.16412 Section 2.1, matching the existing exact_quantum_query_complexity definition.

The probability that the output bit is true after a specified finite-dimensional phase-query circuit on a Boolean input.
-/

/-- Acceptance probability of a finite phase-query circuit. -/
noncomputable def phase_query_acceptance_probability {N q : ℕ}
    {B : Type} [Fintype B] (reg : B → Option (Fin N)) (ψ0 : B → ℂ)
    (U0 : Matrix B B ℂ) (steps : Fin q → Matrix B B ℂ)
    (out : B → Bool) (x : Fin N → Bool) : ℝ :=
  ∑ b, if out b then Complex.normSq
    (((List.ofFn steps).foldl
      (fun v U => Matrix.mulVec U (fun b =>
        (match reg b with | none => (1 : ℂ) | some i => if x i then -1 else 1) * v b))
      (Matrix.mulVec U0 ψ0)) b) else 0
