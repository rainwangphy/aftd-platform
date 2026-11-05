import AFTD.Prelude

/-!
# perm_edit_cost

Topic: graphs   Node: 96ef8051fe10

Provenance: formalization of a published result. Source: arXiv:2611.05048 Section 3, line 325

The edit cost $\mathcal{C}_{\mathsf{ed}}(\pi)$ of a permutation $\pi$ between two $n \times n$ matrices $A$ and $B$ is the sum over all $v, v' \in \{0, \dots, n-1\}$ of $|A(v, v') - B(\pi(v), \pi(v'))|$.
-/

/-- The edit cost of a permutation π between two matrices A and B. -/
def perm_edit_cost {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) (π : Equiv.Perm (Fin n)) : ℝ := ∑ v : Fin n, ∑ v' : Fin n, |A v v' - B (π v) (π v')|
