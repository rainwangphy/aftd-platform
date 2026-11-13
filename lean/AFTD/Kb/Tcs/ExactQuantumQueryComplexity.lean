import AFTD.Prelude

/-!
# exact_quantum_query_complexity

Topic: quantum   Node: a13d0e6be94d

Provenance: formalization of a published result. Source: arXiv:2611.16412 Section 2.1

Exact quantum query complexity Q_E(f) of a Boolean function f on N bits, defined as the minimum number of phase queries needed to evaluate f exactly.
-/

/-- Exact quantum query complexity Q_E(f) of a Boolean function f in the standard phase query model. -/
noncomputable def exact_quantum_query_complexity {N : ℕ} (f : (Fin N → Bool) → Bool) : ℕ := sInf { q : ℕ | ∃ (B : Type) (_ : Fintype B) (_ : DecidableEq B) (reg : B → Option (Fin N)) (ψ0 : B → ℂ) (_ : ∑ b, Complex.normSq (ψ0 b) = 1) (U0 : Matrix B B ℂ) (_ : U0 ∈ Matrix.unitaryGroup B ℂ) (steps : Fin q → Matrix B B ℂ) (_ : ∀ t, steps t ∈ Matrix.unitaryGroup B ℂ) (out : B → Bool), ∀ x : Fin N → Bool, (∑ b, if out b then Complex.normSq (((List.ofFn steps).foldl (fun v U => Matrix.mulVec U (fun b => (match reg b with | none => (1 : ℂ) | some i => if x i then -1 else 1) * v b)) (Matrix.mulVec U0 ψ0)) b) else 0) = if f x then 1 else 0 }
