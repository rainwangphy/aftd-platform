import AFTD.Prelude
import AFTD.Kb.Tcs.CompatibleLabelings
import AFTD.Kb.Tcs.EdgeArrivalProb
import AFTD.Kb.Tcs.OnlineMatchingPolicy

/-!
# policy_value

Topic: online_algorithms   Node: b68e932efa32

Provenance: formalization of a published result. Source: arXiv:2611.13571, Section 5.1

For a simple graph G on vertex set Fin n with decidable adjacency, an online matching policy pol : OnlineMatchingPolicy n, an observed edge set H : Finset (Sym2 (Fin n)), and an unmatched vertex set U : Finset (Fin n), policy_value G pol H U is the expected matching size achieved by pol from state (H, U), defined by recursion on G.edgeFinset.card - H.card: 0 when G.edgeFinset.card - H.card = 0, and otherwise the sum over e : Sym2 (Fin n) with e ∉ H and 0 < compatible_labelings G (insert e H) of edge_arrival_prob G H e multiplied by (if e.toFinset ⊆ U ∧ pol H U e then 1 + policy_value G pol (insert e H) (U \ e.toFinset) else policy_value G pol (insert e H) U).
-/

/-- The expected matching size achieved by an online policy from state (H, U). -/
noncomputable def policy_value {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (pol : OnlineMatchingPolicy n)
    (H : Finset (Sym2 (Fin n))) (U : Finset (Fin n)) : ℝ :=
  aux (G.edgeFinset.card - H.card) H U
where
  aux : ℕ → Finset (Sym2 (Fin n)) → Finset (Fin n) → ℝ
    | 0, _, _ => 0
    | k + 1, H', U' =>
      ∑ e ∈ (Finset.univ : Finset (Sym2 (Fin n))),
        if e ∉ H' ∧ 0 < compatible_labelings G (insert e H') then
          edge_arrival_prob G H' e *
            (if e.toFinset ⊆ U' ∧ pol H' U' e then
              1 + aux k (insert e H') (U' \ e.toFinset)
            else
              aux k (insert e H') U')
        else 0
