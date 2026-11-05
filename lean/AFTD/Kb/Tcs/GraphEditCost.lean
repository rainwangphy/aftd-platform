import AFTD.Prelude

/-!
# graph_edit_cost

Topic: graphs   Node: bffd9ada66a2

Provenance: formalization of a published result. Source: arXiv:2611.05048 Section 2 and Section 3

The edit cost $\mathcal{C}_{\mathsf{ed}}(Q)$ of a fractional alignment matrix $Q$ between two $n \times n$ matrices $A$ and $B$ is the sum over all $v, v', w, w' \in \{0, \dots, n-1\}$ of $|A(v, v') - B(w, w')| Q(v, w) Q(v', w')$.
-/

/-- The edit cost of a fractional alignment matrix Q between two matrices A and B. -/
def graph_edit_cost {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) (Q : Matrix (Fin n) (Fin n) ℝ) : ℝ := ∑ v : Fin n, ∑ v' : Fin n, ∑ w : Fin n, ∑ w' : Fin n,
    |A v v' - B w w'| * Q v w * Q v' w'
