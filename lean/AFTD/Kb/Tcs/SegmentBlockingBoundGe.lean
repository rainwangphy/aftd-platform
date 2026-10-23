import AFTD.Prelude
import AFTD.Kb.Tcs.PointsInGeneralPosition
import AFTD.Kb.Tcs.SegmentEndpoints
import AFTD.Kb.Tcs.SegmentsBlockPointsProp

/-!
# segment_blocking_bound_ge

Topic: online_algorithms   Node: aa1ca8d94ea4

Provenance: formalization of a published result. Source: arXiv:2610.23130 Definition 1.1

For a segment property P on Finset (Sym2 (ℝ × ℝ)) and natural numbers ℓ and p, segment_blocking_bound_ge P ℓ p asserts that there exists a finite family L of ℓ segments satisfying P with 2ℓ pairwise distinct endpoints and a disjoint finite point set S of at least p points such that the endpoints of L and S are jointly in general position and L blocks S under P.
-/

/-- Asserts that the blocking number β_P(ℓ) is at least p: there exists a family of ℓ disjoint segments satisfying P blocking at least p points in general position. -/
def segment_blocking_bound_ge (P : Finset (Sym2 (ℝ × ℝ)) → Prop) (ℓ p : ℕ) : Prop := ∃ (L : Finset (Sym2 (ℝ × ℝ))) (S : Finset (ℝ × ℝ)),
    L.card = ℓ ∧ P L ∧
    (segment_endpoints L).card = 2 * ℓ ∧
    Disjoint (segment_endpoints L) S ∧
    points_in_general_position (segment_endpoints L ∪ S : Set (ℝ × ℝ)) ∧
    segments_block_points_prop P L S ∧
    p ≤ S.card
