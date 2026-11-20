import AFTD.Prelude

/-!
# rotation_free_set_from_cap

Topic: combinatorics   Node: 551b017d90d6

Provenance: formalization of a published result. Source: arXiv:2611.20408, Lemma 2.2

For $n \ge 0$ and $C \subseteq \mathbb{F}_3^n$, $D$ is the finite subset of $(\mathbb{F}_3^2)^n$ consisting of vectors $((s_j, t_j))_{j=0}^{n-1}$ such that $(s_j - t_j)_{j=0}^{n-1} \in C$ and $(s_j)_{j=0}^{n-1} \in C$.
-/

/-- The set $D \subseteq (\mathbb{F}_3^2)^n$ constructed from a cap set $C \subseteq \mathbb{F}_3^n$. -/
def rotation_free_set_from_cap (n : ℕ) (C : Finset (Fin n → ZMod 3)) :
    Finset (Fin n → ZMod 3 × ZMod 3) :=
  Finset.univ.filter (fun ξ => (fun j => (ξ j).1 - (ξ j).2) ∈ C ∧ (fun j => (ξ j).1) ∈ C)
