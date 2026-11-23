import AFTD.Prelude
import AFTD.Kb.Tcs.NatSelfDelimitingCode
import AFTD.Kb.Tcs.RatSegmentListCode

/-!
# cable_instance_code

Topic: approximation   Node: cec7610e0f7e

Provenance: helper lemma. Input encoding, helper for the polynomial-time statement of OP-2019 (arXiv:2611.24611 (Inapproximability of Euclidean Steiner Tree), Section 6.1, after Corollary 20 (open question: is planar Euclidean Cable Steiner Tree APX-hard or does it admit a PTAS?)).

The binary word encoding an instance of planar cable Steiner tree given as a list I of cables, each cable a list of segments with rational endpoints: the number of cables in nat_self_delimiting_code, followed by rat_segment_list_code of each cable in order.
-/

/-- The binary code of a cable instance (a list of cables, each a list of rational segments): the number of cables, then each cable's `rat_segment_list_code`. -/
def cable_instance_code (I : List (List ((ℚ × ℚ) × (ℚ × ℚ)))) : List Bool :=
  nat_self_delimiting_code I.length ++ I.flatMap rat_segment_list_code
