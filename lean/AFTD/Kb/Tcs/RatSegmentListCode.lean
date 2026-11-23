import AFTD.Prelude
import AFTD.Kb.Tcs.NatSelfDelimitingCode
import AFTD.Kb.Tcs.RatSelfDelimitingCode

/-!
# rat_segment_list_code

Topic: approximation   Node: f4da298d1b1a

Provenance: helper lemma. Input/output encoding, helper for the polynomial-time statement of OP-2019 (arXiv:2611.24611 (Inapproximability of Euclidean Steiner Tree), Section 6.1, after Corollary 20 (open question: is planar Euclidean Cable Steiner Tree APX-hard or does it admit a PTAS?)).

The binary word encoding a list S of plane segments, each given by two endpoints ((x1, y1), (x2, y2)) with rational coordinates: the length of S in nat_self_delimiting_code, followed, for each segment of S in order, by the codes rat_self_delimiting_code of x1, y1, x2, y2 in this order.
-/

/-- The binary code of a finite list of plane segments with rational endpoints ((x₁, y₁), (x₂, y₂)): the length of the list, then the four coordinates of each segment in order. -/
def rat_segment_list_code (S : List ((ℚ × ℚ) × (ℚ × ℚ))) : List Bool :=
  nat_self_delimiting_code S.length ++
    S.flatMap (fun s => rat_self_delimiting_code s.1.1 ++ rat_self_delimiting_code s.1.2 ++
      rat_self_delimiting_code s.2.1 ++ rat_self_delimiting_code s.2.2)
