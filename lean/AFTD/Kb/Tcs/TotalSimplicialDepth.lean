import AFTD.Prelude
import AFTD.Kb.Tcs.SimplicialDepth

/-!
# total_simplicial_depth

Topic: combinatorics   Node: fa1a153a9a57

Provenance: formalization of a published result. Source: arXiv:2610.38658, Definition 19

The total simplicial depth TSD(P) of a finite point set P in the Euclidean plane is the sum over all points p in P of the simplicial depth SD(p, P).
-/

/-- Total simplicial depth of a finite point set P in ℝ², defined as the sum of simplicial depths of all points in P. -/
noncomputable def total_simplicial_depth (P : Finset (ℝ × ℝ)) : ℕ := ∑ p ∈ P, simplicial_depth p P
