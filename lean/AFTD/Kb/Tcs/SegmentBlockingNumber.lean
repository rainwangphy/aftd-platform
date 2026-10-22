import AFTD.Prelude
import AFTD.Kb.Tcs.PointsInGeneralPosition
import AFTD.Kb.Tcs.SegmentEndpoints
import AFTD.Kb.Tcs.SegmentsBlockPointsProp

/-!
# segment_blocking_number

Topic: online_algorithms   Node: e4d4831d3739

Provenance: formalization of a published result. Source: arXiv:2610.23130, Definition 1.1

For a predicate P on finite sets of unordered pairs in Sym2 (ℝ × ℝ) and an integer ℓ, the blocking number segment_blocking_number P ℓ is the supremum in ℕ of cardinalities of finite point sets S in ℝ × ℝ for which there exists a family L of ℓ unordered pairs in Sym2 (ℝ × ℝ) satisfying P such that the endpoints of L and points of S are jointly in general position and L blocks S under P.
-/

/-- The blocking number β_P(ℓ) is the maximum size of a point set blocked by ℓ segments satisfying P in general position. -/
noncomputable def segment_blocking_number
    (P : Finset (Sym2 (ℝ × ℝ)) → Prop) (ℓ : ℕ) : ℕ := open scoped Classical in
  sSup { p : ℕ | ∃ (L : Finset (Sym2 (ℝ × ℝ))) (S : Finset (ℝ × ℝ)),
    L.card = ℓ ∧ P L ∧ points_in_general_position (segment_endpoints L ∪ S : Set (ℝ × ℝ)) ∧
    segments_block_points_prop P L S ∧ S.card = p }
