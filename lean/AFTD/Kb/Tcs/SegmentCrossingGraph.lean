import AFTD.Prelude
import AFTD.Kb.Tcs.SegmentCrossing

/-!
# segment_crossing_graph

Topic: combinatorics   Node: 078e5d875d2f

Provenance: formalization of a published result. Source: arXiv:2610.23130 Sec. 1

The crossing graph G(L) of a finite family of line segments L is the simple graph with vertex set L and edges between segments whose relative interiors intersect.
-/

/-- The crossing graph of a finite family of segments in ℝ². -/
def segment_crossing_graph (L : Finset (Sym2 (ℝ × ℝ))) : SimpleGraph L := SimpleGraph.fromRel (fun e₁ e₂ => segment_crossing e₁.1 e₂.1)
