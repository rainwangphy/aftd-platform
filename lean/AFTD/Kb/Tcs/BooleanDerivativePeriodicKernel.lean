import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanDerivative

/-!
# boolean_derivative_periodic_kernel

Topic: cryptography   Node: 06730281d4c6

Provenance: helper lemma. step towards boolean_derivative_conjecture_dim_eight

Any Boolean function h having period v satisfies D_v(h) = 0.
-/

/-- Any Boolean function having period v lies in the kernel of D_v. -/
theorem boolean_derivative_periodic_kernel {n : ℕ} (v : Fin n → ZMod 2) (h : (Fin n → ZMod 2) → ZMod 2) (hh : ∀ x, h (x + v) = h x) : boolean_derivative v h = 0 := by
  funext x
  simp only [boolean_derivative, Pi.zero_apply]
  rw [hh x]
  exact CharTwo.add_self_eq_zero (h x)
