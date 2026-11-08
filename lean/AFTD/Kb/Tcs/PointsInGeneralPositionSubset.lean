import AFTD.Prelude
import AFTD.Kb.Tcs.PointsInGeneralPosition

/-!
# points_in_general_position_subset

Topic: combinatorics   Node: 717ad54117c0

Provenance: helper lemma. arXiv:2610.38658 Lemma 20 -- Larger Crossing Families

Any subset of a point set in general position in the Euclidean plane is also in general position.
-/

/-- Subsets of point sets in general position in ℝ² are in general position. -/
theorem points_in_general_position_subset
    {P Q : Set (ℝ × ℝ)} (hsub : Q ⊆ P) (hgen : points_in_general_position P) :
    points_in_general_position Q := fun _ _ _ h1 h2 h3 => hgen (hsub h1) (hsub h2) (hsub h3)
