import AFTD.Prelude
import AFTD.Kb.Tcs.SegmentCrossingGraph

/-!
# segments_block_points

Topic: combinatorics   Node: 6da4ad990b18

Provenance: formalization of a published result. Source: arXiv:2610.23130 Def. 1.1

A finite family of segments L blocks a finite point set P under the triangle-free crossing property if for every pair of distinct points u, v in P, adding the segment uv to L creates a triangle in the crossing graph.
-/

/-- A family of segments blocks a point set under the triangle-free crossing property. -/
def segments_block_points (L : Finset (Sym2 (ℝ × ℝ))) (P : Finset (ℝ × ℝ)) : Prop := ∀ ⦃u v : ℝ × ℝ⦄, u ∈ P → v ∈ P → u ≠ v →
    ¬ (segment_crossing_graph (insert s(u, v) L)).CliqueFree 3
