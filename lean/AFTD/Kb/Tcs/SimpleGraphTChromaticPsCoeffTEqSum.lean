import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTChromaticPrincipalSpecialization

/-!
# simple_graph_t_chromatic_ps_coeff_t_eq_sum

Topic: graphs   Node: 8dc3ebc6ecf6

Provenance: helper lemma. arXiv:2610.31785 (Principal specializations of the t-chromatic symmetric function), Proposition 3.16(3), the coefficient of t^k as a sum over colorings

For a finite simple graph G and natural numbers n, k, the coefficient of t^k in ps_n(Z_G(x; t)) is the polynomial in q equal to the sum of q^(∑_v c(v)) over the proper colorings c : V → Fin n using exactly k distinct colors.
-/

theorem simple_graph_t_chromatic_ps_coeff_t_eq_sum {V : Type*} [Fintype V] (G : SimpleGraph V) (n k : ℕ) :
    (simple_graph_t_chromatic_principal_specialization G n).coeff k =
      ∑ c ∈ Finset.univ.filter (fun c : G.Coloring (Fin n) => (Finset.univ.image c).card = k),
        Polynomial.X ^ (∑ v : V, (c v : ℕ)) := by
  classical
  unfold simple_graph_t_chromatic_principal_specialization
  rw [Polynomial.finsetSum_coeff, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Polynomial.coeff_monomial, Polynomial.X_pow_eq_monomial]
