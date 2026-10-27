import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTChromaticPrincipalSpecialization
import AFTD.Kb.Tcs.SimpleGraphChromaticPrincipalSpecialization

/-!
# simple_graph_t_chromatic_ps_eval_one

Topic: graphs   Node: 9f8bc2b8c837

Provenance: helper lemma. arXiv:2610.31785, proof of Proposition 3.9

For any finite simple graph G on a finite vertex type V and any natural number n, evaluating the n-th principal specialization of the t-chromatic symmetric function ps_n(Z_G(x; t)) at t = 1 via Polynomial.eval 1 yields the n-th principal specialization of the chromatic symmetric function ps_n(X_G(x)).
-/

/-- Evaluating the n-th principal specialization ps_n(Z_G(x; t)) at t = 1 yields ps_n(X_G(x)). -/
theorem simple_graph_t_chromatic_ps_eval_one {V : Type*} [Fintype V]
    (G : SimpleGraph V) (n : ℕ) :
    Polynomial.eval 1 (simple_graph_t_chromatic_principal_specialization G n) =
      simple_graph_chromatic_principal_specialization G n := by
  simp only [simple_graph_t_chromatic_principal_specialization, simple_graph_chromatic_principal_specialization]
  have h : ∀ p : Polynomial (Polynomial ℕ),
      Polynomial.eval (1 : Polynomial ℕ) p = Polynomial.evalRingHom 1 p := fun p => rfl
  rw [h, map_sum]
  simp [Polynomial.eval_monomial]
