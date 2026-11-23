import AFTD.Prelude
import AFTD.Kb.Tcs.RatSegmentsUnion

/-!
# cable_steiner_opt

Topic: approximation   Node: 60479915e54a

Provenance: formalization of a published result. Source: arXiv:2611.24611 (Inapproximability of Euclidean Steiner Tree), Definition 5 (Euclidean Cable Steiner Tree), in the plane; the optimum is written as an infimum over feasible networks.

For a list I of cables in the plane, each cable given as a list of segments, a segment being a pair of endpoints each given as a pair (x, y) ∈ ℚ × ℚ of rational coordinates (the type List (List ((ℚ × ℚ) × (ℚ × ℚ))), with a point (x, y) read as the point of EuclideanSpace ℝ (Fin 2) with coordinates x, y; a cable is the union rat_segments_union of the closed segments between its listed endpoints), the optimum of Euclidean Cable Steiner Tree: the infimum (sInf of a set of reals) of the total Euclidean length Σ dist(a, b) over all finite sets T of pairs (a, b) of points of EuclideanSpace ℝ (Fin 2) such that the union of all cables (the union of their closed segments) together with the union of the closed segments [a, b], (a, b) ∈ T, is a connected (nonempty) subset of the plane.
-/

/-- The optimum of planar Euclidean Cable Steiner Tree: the infimum of the total length of a finite set of added segments (arbitrary real endpoints, i.e. Steiner points anywhere) whose union with the cables is connected. -/
noncomputable def cable_steiner_opt (I : List (List ((ℚ × ℚ) × (ℚ × ℚ)))) : ℝ :=
  sInf {L : ℝ | ∃ T : Finset (EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2)),
    IsConnected ((⋃ c ∈ I, rat_segments_union c) ∪ ⋃ t ∈ T, segment ℝ t.1 t.2) ∧
    L = ∑ t ∈ T, dist t.1 t.2}
