import AFTD.Prelude

/-!
# pyranim_gamma

Topic: combinatorial_games   Node: 638e0672aadf

Provenance: formalization of a published result. Source: arXiv:2611.16153 Def. 2.4

For a finite set of chips X : Finset (ℕ × ℕ), pyranim_gamma X is the simple graph with vertex set given by the subtype {i : ℕ // (i, i) ∈ X} where two distinct vertices u, v are adjacent if and only if (min u.val v.val, max u.val v.val) ∈ X.
-/

/-- The unit interval graph Gamma(X) associated to a Pyranim position X. -/
def pyranim_gamma (X : Finset (ℕ × ℕ)) : SimpleGraph {i : ℕ // (i, i) ∈ X} := SimpleGraph.fromRel (fun u v => (min u.1 v.1, max u.1 v.1) ∈ X)
