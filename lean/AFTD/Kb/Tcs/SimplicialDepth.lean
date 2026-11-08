import AFTD.Prelude

/-!
# simplicial_depth

Topic: combinatorics   Node: 0b4fb0cf33e2

Provenance: formalization of a published result. Source: arXiv:2610.38658, Definition 19

The simplicial depth SD(p, P) of a point p with respect to a finite set P in the Euclidean plane is the number of 3-element subsets of P \ {p} whose open triangle contains p.
-/

/-- Simplicial depth of a point p with respect to a finite set P in ℝ². -/
noncomputable def simplicial_depth (p : ℝ × ℝ) (P : Finset (ℝ × ℝ)) : ℕ := open Classical in (((P.erase p).powersetCard 3).filter (fun (T : Finset (ℝ × ℝ)) => p ∈ interior (convexHull ℝ (T : Set (ℝ × ℝ))))).card
