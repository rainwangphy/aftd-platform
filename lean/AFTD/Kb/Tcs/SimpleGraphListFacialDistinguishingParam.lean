import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphHasListFacialDistinguishingLabeling

/-!
# simple_graph_list_facial_distinguishing_param

Topic: combinatorics   Node: 4915b5e7bd7c

Provenance: formalization of a published result. Source: arXiv:2611.18384 Definition 2.1

The list adjacent-facial-sum-distinguishing labeling parameter $\lambda_\ell(G, \sigma)$ of a simple graph $G$ equipped with a dart permutation $\sigma$ is the least integer $k \ge 0$ such that $G$ admits an adjacent-facial-sum-distinguishing proper vertex labeling from arbitrary real lists of size $k + 1$ with respect to the faces induced by $\sigma$.
-/

/-- The list facial-sum-distinguishing labeling parameter λ_ℓ(G). -/
noncomputable def simple_graph_list_facial_distinguishing_param {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (σ : Equiv.Perm G.Dart) : ℕ :=
  sInf {k : ℕ | simple_graph_has_list_facial_distinguishing_labeling G σ k}
