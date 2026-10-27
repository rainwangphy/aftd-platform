import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTChromaticPrincipalSpecialization
import AFTD.Kb.Tcs.SimpleGraphChromaticPrincipalSpecialization
import AFTD.Kb.Tcs.SimpleGraphTChromaticPsEvalOne

/-!
# simple_graph_t_chromatic_ps_determines_chromatic_ps

Topic: graphs   Node: ac019c14c156

Provenance: formalization of a published result. Source: arXiv:2610.31785, Proposition 3.9

Let G and H be finite simple graphs on finite vertex types V and W, respectively, and let n be a positive integer. If the n-th principal specialization of the t-chromatic symmetric function of G equals that of H, then the n-th principal specialization of the chromatic symmetric function of G equals that of H.
-/

/-- Proposition 3.9: Equality of the n-th principal specializations of the t-chromatic symmetric function implies equality of the principal specializations of the chromatic symmetric function. -/
theorem simple_graph_t_chromatic_ps_determines_chromatic_ps
    {V W : Type*} [Fintype V] [Fintype W]
    (G : SimpleGraph V) (H : SimpleGraph W) (n : ℕ) (_hn : 0 < n)
    (h : simple_graph_t_chromatic_principal_specialization G n =
         simple_graph_t_chromatic_principal_specialization H n) :
    simple_graph_chromatic_principal_specialization G n =
      simple_graph_chromatic_principal_specialization H n := by
  rw [← simple_graph_t_chromatic_ps_eval_one G n,
    ← simple_graph_t_chromatic_ps_eval_one H n, h]
