import AFTD.Prelude
import AFTD.Kb.Tcs.CompatibleLabelings

/-!
# edge_arrival_prob

Topic: online_algorithms   Node: 0748475f905f

Provenance: formalization of a published result. Source: arXiv:2611.13571, Section 5.1, Equation (13)

For a simple graph G on vertex set Fin n with decidable adjacency, a finite set H : Finset (Sym2 (Fin n)) of observed edges, and an edge e : Sym2 (Fin n), edge_arrival_prob G H e is defined as (compatible_labelings G (insert e H) : ℝ) / ((G.edgeFinset.card - H.card : ℝ) * (compatible_labelings G H : ℝ)) if the denominator is nonzero, and 0 otherwise.
-/

/-- The transition probability p(e | H) that edge e arrives next given observed edges H. -/
noncomputable def edge_arrival_prob {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (H : Finset (Sym2 (Fin n))) (e : Sym2 (Fin n)) : ℝ :=
  if (G.edgeFinset.card - H.card : ℝ) * (compatible_labelings G H : ℝ) = 0 then 0
  else (compatible_labelings G (insert e H) : ℝ) /
    ((G.edgeFinset.card - H.card : ℝ) * (compatible_labelings G H : ℝ))
