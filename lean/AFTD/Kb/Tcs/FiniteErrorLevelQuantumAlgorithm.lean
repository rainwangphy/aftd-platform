import AFTD.Prelude
import AFTD.Kb.Tcs.PhaseQueryAcceptanceProbability

/-!
# finite_error_level_quantum_algorithm

Topic: quantum   Node: 9646cb65be05

Provenance: helper lemma. Circuit model of arXiv:2611.16412 Section 2.1; error-level condition introduced as a helper for OP-1638.

There is a normalized q-query unitary phase-query circuit computing f with error probability at most one third on every input, and the set of its distinct input-dependent error probabilities has cardinality at most m.
-/

/-- A bounded-error phase-query circuit with at most m distinct error probabilities. -/
def finite_error_level_quantum_algorithm {N : ℕ} (f : (Fin N → Bool) → Bool)
    (q m : ℕ) : Prop :=
  ∃ (B : Type) (_ : Fintype B) (_ : DecidableEq B)
    (reg : B → Option (Fin N)) (ψ0 : B → ℂ)
    (_ : ∑ b, Complex.normSq (ψ0 b) = 1)
    (U0 : Matrix B B ℂ) (_ : U0 ∈ Matrix.unitaryGroup B ℂ)
    (steps : Fin q → Matrix B B ℂ) (_ : ∀ t, steps t ∈ Matrix.unitaryGroup B ℂ)
    (out : B → Bool),
      let p := phase_query_acceptance_probability reg ψ0 U0 steps out
      (∀ x, |p x - (if f x then (1 : ℝ) else 0)| ≤ 1 / 3) ∧
      (Set.range (fun x => if f x then 1 - p x else p x)).ncard ≤ m
