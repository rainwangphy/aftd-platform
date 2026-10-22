import AFTD.Prelude
import AFTD.Kb.Tcs.StarGraphK1

/-!
# star_forest

Topic: graphs   Node: 2614e1a8c5db

Provenance: formalization of a published result. Source: arXiv:2610.25958

The disjoint union of $q$ stars with sizes given by $n : \text{Fin } q \to \mathbb{N}$, on vertices $\Sigma (i : \text{Fin } q), \text{Option}(\text{Fin}(n(i)))$.
-/

/-- Disjoint union of q star graphs with leaf counts given by n : Fin q → ℕ. -/
def star_forest {q : ℕ} (n : Fin q → ℕ) : SimpleGraph ((i : Fin q) × Option (Fin (n i))) := SimpleGraph.fromRel fun u v => ∃ h : u.1 = v.1, (star_graph_k1 (n u.1)).Adj u.2 (h ▸ v.2)
