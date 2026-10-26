import AFTD.Prelude
import AFTD.Kb.Tcs.MatroidConnectivity

/-!
# IsKConnectedSet

Topic: combinatorics   Node: 36f01c4db32e

Provenance: formalization of a published result. Source: arXiv:2610.29979, Section 1

A set $Z$ in a matroid $M$ is $k$-connected for an integer $k \ge 2$ if for every subset $A \subseteq E(M)$, the connectivity function satisfies $\lambda_M(A) \ge \min(|Z \cap A|, |Z \setminus A|, k - 1)$.
-/

/-- A subset Z of elements of a matroid M is k-connected if λ(A) ≥ min(|Z ∩ A|, |Z \ A|, k - 1) for all A ⊆ E(M). -/
def IsKConnectedSet {α : Type*} (M : Matroid α) (k : ℕ) (Z : Set α) : Prop := ∀ A ⊆ M.E, min (min (Z ∩ A).ncard (Z \ A).ncard) (k - 1) ≤ matroid_connectivity M A
