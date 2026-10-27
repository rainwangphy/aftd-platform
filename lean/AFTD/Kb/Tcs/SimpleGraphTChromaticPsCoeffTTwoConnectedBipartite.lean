import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTChromaticPrincipalSpecialization
import AFTD.Kb.Tcs.SimpleGraphTChromaticPsCoeffTTwoOfEdge
import AFTD.Kb.Tcs.FinPairNeSumPowSwap

/-!
# simple_graph_t_chromatic_ps_coeff_t_two_connected_bipartite

Topic: graphs   Node: cda0993d4196

Provenance: formalization of a published result. Source: arXiv:2610.31785 (Principal specializations of the t-chromatic symmetric function), Proposition 3.16(3); the bipartition is given as a proper 2-coloring b, whose parts are the unique bipartition of the connected graph

Let n ≥ 2 and let G be a connected finite simple graph with at least 2 vertices that has a proper coloring with n colors, and let b : V → Fin 2 be a proper 2-coloring of G (so G is bipartite). Let c1 and c2 be the smaller and the larger of the sizes of the two parts {v | b v = 0} and {v | b v = 1}. Then the coefficient of t^2 in ps_n(Z_G(x; t)) equals the sum over ordered pairs (j1, j2) of distinct elements of {0, ..., n-1} of q^(c1 j1 + c2 j2).
-/

theorem simple_graph_t_chromatic_ps_coeff_t_two_connected_bipartite_fin_two (a : Fin 2) : ¬ a = 0 ↔ a = 1 := by fin_cases a <;> decide

theorem simple_graph_t_chromatic_ps_coeff_t_two_connected_bipartite {V : Type*} [Fintype V] (G : SimpleGraph V) (n : ℕ) (hn : 2 ≤ n)
    (hV : 2 ≤ Fintype.card V) (hcol : G.Colorable n) (hconn : G.Connected)
    (b : G.Coloring (Fin 2)) :
    (simple_graph_t_chromatic_principal_specialization G n).coeff 2 =
      ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 ≠ p.2),
        Polynomial.X ^ (min (Finset.univ.filter (fun v => b v = 0)).card
                            (Finset.univ.filter (fun v => b v = 1)).card * (p.1 : ℕ) +
                        max (Finset.univ.filter (fun v => b v = 0)).card
                            (Finset.univ.filter (fun v => b v = 1)).card * (p.2 : ℕ)) := by
  classical
  obtain ⟨x, y, hxy⟩ := Fintype.exists_pair_of_one_lt_card (by omega : 1 < Fintype.card V)
  obtain ⟨p⟩ := hconn.preconnected x y
  have : ∃ u w, G.Adj u w := by
    cases p with
    | nil => exact absurd rfl hxy
    | cons h _ => exact ⟨_, _, h⟩
  obtain ⟨u, w, huw⟩ := this
  have hbuw := b.valid huw
  have key : ∃ u0 w0, b u0 = 0 ∧ b w0 = 1 ∧ G.Adj u0 w0 := by
    by_cases hu : b u = 0
    · exact ⟨u, w, hu, (simple_graph_t_chromatic_ps_coeff_t_two_connected_bipartite_fin_two _).1 (fun h => hbuw (hu.trans h.symm)), huw⟩
    · exact ⟨w, u, by rw [simple_graph_t_chromatic_ps_coeff_t_two_connected_bipartite_fin_two] at hu; by_contra h; rw [simple_graph_t_chromatic_ps_coeff_t_two_connected_bipartite_fin_two] at h; exact hbuw (hu.trans h.symm),
        (simple_graph_t_chromatic_ps_coeff_t_two_connected_bipartite_fin_two _).1 hu, huw.symm⟩
  obtain ⟨u0, w0, hb0, hb1, hadj⟩ := key
  rw [simple_graph_t_chromatic_ps_coeff_t_two_of_edge G n hconn b u0 w0 hb0 hb1 hadj]
  rcases le_total (Finset.univ.filter (fun v => b v = 0)).card
      (Finset.univ.filter (fun v => b v = 1)).card with h | h
  · rw [min_eq_left h, max_eq_right h]
  · rw [min_eq_right h, max_eq_left h, fin_pair_ne_sum_pow_swap]
