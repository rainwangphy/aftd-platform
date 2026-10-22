import AFTD.Prelude

/-!
# segments_block_points_prop

Topic: online_algorithms   Node: ce959e8e748e

Provenance: formalization of a published result. Source: arXiv:2610.23130, Definition 1.1

For a predicate P on finite sets of unordered pairs in Sym2 (ℝ × ℝ), a finite set L of unordered pairs in Sym2 (ℝ × ℝ), and a finite set S of points in ℝ × ℝ, segments_block_points_prop P L S asserts that for every pair of distinct points u, v in S, P does not hold on the insertion of the unordered pair s(u, v) into L.
-/

/-- A segment family L blocks a point set S under property P if adding any segment between distinct points of S violates P. -/
def segments_block_points_prop (P : Finset (Sym2 (ℝ × ℝ)) → Prop)
    (L : Finset (Sym2 (ℝ × ℝ))) (S : Finset (ℝ × ℝ)) : Prop := ∀ ⦃u v : ℝ × ℝ⦄, u ∈ S → v ∈ S → u ≠ v → ¬ P (insert s(u, v) L)
