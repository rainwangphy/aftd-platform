import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTChromaticPrincipalSpecialization
import AFTD.Kb.Tcs.SimpleGraphTChromaticPsCoeffCoeff
import AFTD.Kb.Tcs.SimpleGraphTChromaticPsColoringCountRev
import AFTD.Kb.Tcs.SimpleGraphTChromaticPsMinAddMaxQDegree

/-!
# simple_graph_t_chromatic_ps_q_coeff_symm

Topic: graphs   Node: 3690cd8f0b57

Provenance: formalization of a published result. Source: arXiv:2610.31785 (Principal specializations of the t-chromatic symmetric function), Proposition 3.16(2)

Let n ≥ 2 and let G be a finite simple graph with at least 2 vertices that has a proper coloring with n colors. Let d and D be the minimum and maximum degrees of q appearing in ps_n(Z_G(x; t)). Then for every j with d ≤ j ≤ D, the coefficient of q^j in ps_n(Z_G(x; t)) (a polynomial in t) equals the coefficient of q^(d+D-j); that is, for every k the coefficients of t^k q^j and t^k q^(d+D-j) agree.
-/

theorem simple_graph_t_chromatic_ps_q_coeff_symm {V : Type*} [Fintype V] (G : SimpleGraph V) (n : ℕ) (hn : 2 ≤ n)
    (hV : 2 ≤ Fintype.card V) (hcol : G.Colorable n) (d D : ℕ)
    (hd : IsLeast {j | ∃ k, ((simple_graph_t_chromatic_principal_specialization G n).coeff k).coeff j ≠ 0} d)
    (hD : IsGreatest {j | ∃ k, ((simple_graph_t_chromatic_principal_specialization G n).coeff k).coeff j ≠ 0} D) :
    ∀ j, d ≤ j → j ≤ D → ∀ k,
      ((simple_graph_t_chromatic_principal_specialization G n).coeff k).coeff j =
        ((simple_graph_t_chromatic_principal_specialization G n).coeff k).coeff (d + D - j) := by
  intro j _ hjD k
  have h := simple_graph_t_chromatic_ps_min_add_max_q_degree G n d D hd hD
  rw [simple_graph_t_chromatic_ps_coeff_coeff, simple_graph_t_chromatic_ps_coeff_coeff, simple_graph_t_chromatic_ps_coloring_count_rev G n k j (by omega), h]
