import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTChromaticPrincipalSpecialization

/-!
# simple_graph_t_chromatic_ps_coeff_coeff

Topic: graphs   Node: 51bbe3526abc

Provenance: helper lemma. arXiv:2610.31785 (Principal specializations of the t-chromatic symmetric function), Proposition 3.16 (equation (3.1): the coefficients count proper colorings by number of colors and weight)

For a finite simple graph G and natural numbers n, k, j, the coefficient of t^k q^j in the n-th principal specialization ps_n(Z_G(x; t)) (simple_graph_t_chromatic_principal_specialization G n, outer variable t, inner variable q) equals the number of proper colorings c : V → Fin n that use exactly k distinct colors and have weight ∑_v c(v) = j.
-/

theorem simple_graph_t_chromatic_ps_coeff_coeff {V : Type*} [Fintype V] (G : SimpleGraph V) (n k j : ℕ) :
    ((simple_graph_t_chromatic_principal_specialization G n).coeff k).coeff j =
      Fintype.card {c : G.Coloring (Fin n) //
        (Finset.univ.image c).card = k ∧ ∑ v : V, (c v : ℕ) = j} := by
  classical
  unfold simple_graph_t_chromatic_principal_specialization
  rw [Polynomial.finsetSum_coeff, Polynomial.finsetSum_coeff]
  simp only [Polynomial.coeff_monomial]
  rw [Fintype.card_subtype]
  rw [Finset.card_eq_sum_ones, Finset.sum_filter]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  by_cases h1 : (Finset.univ.image c).card = k <;> by_cases h2 : ∑ v : V, (c v : ℕ) = j <;>
    simp [h1, h2, Polynomial.coeff_monomial]
