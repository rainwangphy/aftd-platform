import AFTD.Prelude
import AFTD.Kb.Tcs.TwoDistinctPairsInThreeColorsIntersect

/-!
# equal_external_triple_forces_shared_exposed_color

Topic: combinatorics   Node: 8a943cf4fb51

Provenance: helper lemma. Local compatibility obstruction for strong cubic truncation colorings.

If two degree-three vertices have the same three external colors, their two distinct exposed internal-color pairs share a color.
-/

theorem equal_external_triple_forces_shared_exposed_color
    (low a b x y u v : Fin 6)
    (hla : low ≠ a) (hlb : low ≠ b) (hab : a ≠ b)
    (hx : x ≠ low ∧ x ≠ a ∧ x ≠ b)
    (hy : y ≠ low ∧ y ≠ a ∧ y ≠ b)
    (hu : u ≠ low ∧ u ≠ a ∧ u ≠ b)
    (hv : v ≠ low ∧ v ≠ a ∧ v ≠ b)
    (hxy : x ≠ y) (huv : u ≠ v) : x = u ∨ x = v ∨ y = u ∨ y = v := by
  let P : Finset (Fin 6) := Finset.univ \ {low, a, b}
  have hP : P.card = 3 := by
    dsimp [P]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp [hla, hlb, hab]
  have hxP : x ∈ P := by simpa [P] using hx
  have hyP : y ∈ P := by simpa [P] using hy
  have huP : u ∈ P := by simpa [P] using hu
  have hvP : v ∈ P := by simpa [P] using hv
  exact two_distinct_pairs_in_three_colors_intersect P hP x y u v hxP hyP huP hvP hxy huv
