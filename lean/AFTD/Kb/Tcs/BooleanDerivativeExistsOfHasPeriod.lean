import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanDerivative

/-!
# boolean_derivative_exists_of_has_period

Topic: cryptography   Node: 6e52d698c0ce

Provenance: helper lemma. step towards boolean_derivative_conjecture_dim_eight

For any nonzero period v of a Boolean function f, there exists some Boolean function g such that the directional derivative of g along v is f.
-/

/-- Every Boolean function with period v is the directional derivative of some Boolean function along v. -/
theorem boolean_derivative_exists_of_has_period {n : ℕ} (v : Fin n → ZMod 2) (hv : v ≠ 0) (f : (Fin n → ZMod 2) → ZMod 2) (hf : ∀ x, f (x + v) = f x) : ∃ g : (Fin n → ZMod 2) → ZMod 2, boolean_derivative v g = f := by
  have : ∃ i, v i ≠ 0 := by
    by_contra! h
    exact hv (funext h)
  rcases this with ⟨i, hi⟩
  have hvi : v i = 1 := by
    generalize hv_i : v i = a at *
    fin_cases a
    · contradiction
    · rfl
  use fun x => x i * f x
  ext x
  dsimp [boolean_derivative]
  rw [hf, hvi]
  have h2 : (2 : ZMod 2) = 0 := rfl
  linear_combination (x i * f x) * h2
