import AFTD.Prelude
import AFTD.Kb.Tcs.ConnSetPoly

/-!
# conn_set_poly_Q

Topic: graphs   Node: 4cbc39022356

Provenance: helper lemma. step towards op_599_connected_induced_activity_clique_minimum

The defect polynomial Q_G = ((1+X)^n - 1) * Z_G' - n * (1+X)^(n-1) * Z_G, which measures the deviation of the weighted mean order of G from that of K_n.
-/

open scoped BigOperators Polynomial Classical in
/-- Q_G = ((1+X)^n − 1)·Z_G′ − n·(1+X)^(n−1)·Z_G. -/
noncomputable def conn_set_poly_Q {V : Type*} [Fintype V] (G : SimpleGraph V) : Polynomial ℝ := ((1 + Polynomial.X) ^ Fintype.card V - 1) * Polynomial.derivative (conn_set_poly G)
    - Polynomial.C (Fintype.card V : ℝ) * (1 + Polynomial.X) ^ (Fintype.card V - 1) * conn_set_poly G
