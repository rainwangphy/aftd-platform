import AFTD.Prelude

/-!
# phase_query_computes_cleanly

Topic: quantum   Node: 4a495a9bbb5e

Provenance: helper lemma. Clean phase-circuit model of arXiv:2611.16412 Section 2.1, using the same phase queries as exact_quantum_query_complexity.

There is a normalized finite-dimensional q-query unitary phase-query circuit that returns its initial state with phase (-1) to the power f(x) on every Boolean input x.
-/

/-- A clean phase oracle implemented using q queries. -/
def phase_query_computes_cleanly {N : ℕ}
    (f : (Fin N → Bool) → Bool) (q : ℕ) : Prop :=
  ∃ (B : Type) (_ : Fintype B) (_ : DecidableEq B)
    (reg : B → Option (Fin N)) (ψ0 : B → ℂ)
    (_ : ∑ b, Complex.normSq (ψ0 b) = 1)
    (U0 : Matrix B B ℂ) (_ : U0 ∈ Matrix.unitaryGroup B ℂ)
    (steps : Fin q → Matrix B B ℂ) (_ : ∀ t, steps t ∈ Matrix.unitaryGroup B ℂ),
    ∀ x : Fin N → Bool, ∀ b : B,
      ((List.ofFn steps).foldl
        (fun v U => Matrix.mulVec U (fun b =>
          (match reg b with | none => (1 : ℂ) | some i => if x i then -1 else 1) * v b))
        (Matrix.mulVec U0 ψ0)) b = (if f x then (-1 : ℂ) else 1) * ψ0 b
