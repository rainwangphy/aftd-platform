import AFTD.Prelude
import AFTD.Kb.Tcs.CompatibleLabelings
import AFTD.Kb.Tcs.EdgeArrivalProb

/-!
# bellman_value

Topic: online_algorithms   Node: 2a1fd76ede89

Provenance: formalization of a published result. Source: arXiv:2611.13571, Section 5.1, Equation (14)

For a simple graph G on vertex set Fin n with decidable adjacency, an observed edge set H : Finset (Sym2 (Fin n)), and an unmatched vertex set U : Finset (Fin n), bellman_value G H U is the dynamic programming value function V(H, U) defined backwards by recursion on G.edgeFinset.card - H.card: 0 when G.edgeFinset.card - H.card = 0, and otherwise the sum over e : Sym2 (Fin n) satisfying e ∉ H and 0 < compatible_labelings G (insert e H) of edge_arrival_prob G H e multiplied by (if e.toFinset ⊆ U then max (bellman_value G (insert e H) U) (1 + bellman_value G (insert e H) (U \ e.toFinset)) else bellman_value G (insert e H) U).
-/

/-- The optimal value function V(H, U) defined backwards from V(H, U) = 0 when |E(H)| = m. -/
noncomputable def bellman_value {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (H : Finset (Sym2 (Fin n))) (U : Finset (Fin n)) : ℝ :=
  aux (G.edgeFinset.card - H.card) H U
where
  aux : ℕ → Finset (Sym2 (Fin n)) → Finset (Fin n) → ℝ
    | 0, _, _ => 0
    | k + 1, H', U' =>
      ∑ e ∈ (Finset.univ : Finset (Sym2 (Fin n))),
        if e ∉ H' ∧ 0 < compatible_labelings G (insert e H') then
          edge_arrival_prob G H' e *
            (if e.toFinset ⊆ U' then
              max (aux k (insert e H') U') (1 + aux k (insert e H') (U' \ e.toFinset))
            else
              aux k (insert e H') U')
        else 0
