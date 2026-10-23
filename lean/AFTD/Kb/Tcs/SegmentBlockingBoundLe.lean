import AFTD.Prelude
import AFTD.Kb.Tcs.PointsInGeneralPosition
import AFTD.Kb.Tcs.SegmentEndpoints
import AFTD.Kb.Tcs.SegmentsBlockPointsProp

/-!
# segment_blocking_bound_le

Topic: online_algorithms   Node: 940e51a05d37

Provenance: formalization of a published result. Source: arXiv:2610.23130 Definition 1.1

For a segment property P on Finset (Sym2 (ℝ × ℝ)) and natural numbers ℓ and p, segment_blocking_bound_le P ℓ p asserts that every finite family L of ℓ segments satisfying P blocks at most p points in any finite point set S such that the endpoints of L and S are jointly in general position.
-/

/-- Asserts that the blocking number β_P(ℓ) is at most p: every family of ℓ segments satisfying P blocks at most p points in general position. -/
def segment_blocking_bound_le (P : Finset (Sym2 (ℝ × ℝ)) → Prop) (ℓ p : ℕ) : Prop := ∀ (L : Finset (Sym2 (ℝ × ℝ))) (S : Finset (ℝ × ℝ)),
    L.card = ℓ → P L →
    points_in_general_position (segment_endpoints L ∪ S : Set (ℝ × ℝ)) →
    segments_block_points_prop P L S → S.card ≤ p
