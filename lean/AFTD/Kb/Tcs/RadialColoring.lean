import AFTD.Prelude

/-!
# radial_coloring

Topic: combinatorics   Node: 1390beb5aa62

Provenance: helper lemma. step towards op_1481_avoidance_three_twenty_one_exceptional_spacings

The radial two-colouring of Euclidean space attached to a set S ⊆ ℝ: a point x is coloured true exactly when its squared norm ‖x‖² lies in S.
-/

open Classical in
/-- The radial colouring of `EuclideanSpace ℝ (Fin n)` induced by a set `S ⊆ ℝ`: `x` is coloured true iff `‖x‖ ^ 2 ∈ S`. -/
noncomputable def radial_coloring (S : Set ℝ) {n : ℕ} (x : EuclideanSpace ℝ (Fin n)) : Bool := if ‖x‖ ^ 2 ∈ S then true else false
