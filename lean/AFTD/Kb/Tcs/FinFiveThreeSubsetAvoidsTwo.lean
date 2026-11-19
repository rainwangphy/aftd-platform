import AFTD.Prelude

/-!
# fin_five_three_subset_avoids_two

Topic: combinatorics   Node: 1c9f75653724

Provenance: helper lemma. Exceptional five-vertex contraction case in the OP-874 matching-cut reduction.

A five-element set has a three-element subset different from either of two prescribed subsets.
-/

theorem fin_five_three_subset_avoids_two (A B : Finset (Fin 5)) :
    ∃ S : Finset (Fin 5), S.card = 3 ∧ S ≠ A ∧ S ≠ B := by
  let X : Finset (Fin 5) := {0,1,2}
  let Y : Finset (Fin 5) := {0,1,3}
  let Z : Finset (Fin 5) := {0,1,4}
  have hXY : X ≠ Y := by decide
  have hXZ : X ≠ Z := by decide
  have hYZ : Y ≠ Z := by decide
  have hX : X.card = 3 := by decide
  have hY : Y.card = 3 := by decide
  have hZ : Z.card = 3 := by decide
  by_cases hXA : X = A
  · by_cases hYB : Y = B
    · refine ⟨Z, hZ, ?_, ?_⟩
      · intro hZA
        exact hXZ (hXA.trans hZA.symm)
      · intro hZB
        exact hYZ (hYB.trans hZB.symm)
    · refine ⟨Y, hY, ?_, hYB⟩
      intro hYA
      exact hXY (hXA.trans hYA.symm)
  · by_cases hXB : X = B
    · by_cases hYA : Y = A
      · refine ⟨Z, hZ, ?_, ?_⟩
        · intro hZA
          exact hYZ (hYA.trans hZA.symm)
        · intro hZB
          exact hXZ (hXB.trans hZB.symm)
      · refine ⟨Y, hY, hYA, ?_⟩
        intro hYB
        exact hXY (hXB.trans hYB.symm)
    · exact ⟨X, hX, hXA, hXB⟩
