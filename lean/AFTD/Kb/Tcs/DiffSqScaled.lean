import AFTD.Prelude

/-!
# diff_sq_scaled

Topic: combinatorics   Node: cfbb9f9fa2cf

Provenance: formalization of a published result. Source: arXiv:2610.34758 Section 1.3 and Lemma 2.3

The scaled squared difference set $\kappa (A - A)^2$ for a subset $A \subset \mathbb{Z}/p\mathbb{Z}$ and scalar $\kappa \in \mathbb{Z}/p\mathbb{Z}$, defined as $\{\kappa (a - b)^2 : a, b \in A\}$.
-/

/-- The scaled squared difference set kappa * (A - A)^2 in ZMod p. -/
def diff_sq_scaled {p : ℕ} (κ : ZMod p) (A : Set (ZMod p)) : Set (ZMod p) := { κ * (a - b) ^ 2 | (a ∈ A) (b ∈ A) }
