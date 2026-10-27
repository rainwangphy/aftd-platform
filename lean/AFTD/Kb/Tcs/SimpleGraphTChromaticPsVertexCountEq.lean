import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTChromaticPrincipalSpecialization
import AFTD.Kb.Tcs.SimpleGraphTChromaticPsMinAddMaxQDegree

/-!
# simple_graph_t_chromatic_ps_vertex_count_eq

Topic: graphs   Node: daba3a3ffd7b

Provenance: formalization of a published result. Source: arXiv:2610.31785 (Principal specializations of the t-chromatic symmetric function), Proposition 3.16(1)

Let n ≥ 2 and let G be a finite simple graph with at least 2 vertices that has a proper coloring with n colors (χ_G(n) > 0). Let d and D be the minimum and maximum degrees of q appearing in the n-th principal specialization ps_n(Z_G(x; t)) (the least and greatest j such that the coefficient of t^k q^j is nonzero for some k). Then the number of vertices of G equals (d + D)/(n - 1), computed in ℚ.
-/

theorem simple_graph_t_chromatic_ps_vertex_count_eq {V : Type*} [Fintype V] (G : SimpleGraph V) (n : ℕ) (hn : 2 ≤ n)
    (hV : 2 ≤ Fintype.card V) (hcol : G.Colorable n) (d D : ℕ)
    (hd : IsLeast {j | ∃ k, ((simple_graph_t_chromatic_principal_specialization G n).coeff k).coeff j ≠ 0} d)
    (hD : IsGreatest {j | ∃ k, ((simple_graph_t_chromatic_principal_specialization G n).coeff k).coeff j ≠ 0} D) :
    (Fintype.card V : ℚ) = ((d : ℚ) + D) / ((n : ℚ) - 1) := by
  have h := simple_graph_t_chromatic_ps_min_add_max_q_degree G n d D hd hD
  have hn' : ((n : ℚ) - 1) ≠ 0 := by
    have : (2 : ℚ) ≤ n := by exact_mod_cast hn
    linarith
  rw [eq_div_iff hn']
  have h' : ((n - 1 : ℕ) : ℚ) * (Fintype.card V : ℚ) = (d : ℚ) + D := by exact_mod_cast h
  rw [Nat.cast_sub (by omega)] at h'
  push_cast at h'
  linarith
