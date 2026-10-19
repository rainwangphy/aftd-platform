import AFTD.Prelude
import AFTD.Kb.Tcs.CssZDistanceGeThree
import AFTD.Kb.Tcs.CssZDistanceGeThreeIffMultiplicityFree

/-!
# css_z_distance_ge_three_iff_cols

Topic: quantum   Node: bad0f757ffbc

Provenance: helper lemma. arXiv:2610.09341 Lemma 2.1

A CSS quantum code specified by a k by n logical X-operator matrix K and an s by n X-stabilizer matrix S over ZMod 2 has Z-distance at least 3 if and only if its columns are multiplicity-free: no column has zero syndrome with nonzero logical label, and no two distinct columns have equal syndrome but different logical labels.
-/

/-- Z-distance at least 3 is equivalent to multiplicity-free columns. -/
theorem css_z_distance_ge_three_iff_cols {k s n : ℕ}
    (K : Matrix (Fin k) (Fin n) (ZMod 2)) (S : Matrix (Fin s) (Fin n) (ZMod 2)) :
    css_z_distance_ge_three K S ↔
      ((∀ j, S.transpose j = 0 → K.transpose j = 0) ∧
        (∀ i j, i ≠ j → S.transpose i = S.transpose j → K.transpose i = K.transpose j)) := by
  unfold css_z_distance_ge_three
  exact css_z_distance_ge_three_iff_multiplicity_free K S
