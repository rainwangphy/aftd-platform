import AFTD.Prelude
import AFTD.Kb.Tcs.BinaryQuarticRelationsRankLeTwo
import AFTD.Kb.Tcs.BinaryQuadraticPolarQuarticRelation

/-!
# binary_quadratic_polar_rank_le_two_of_fourth_difference

Topic: quantum   Node: 9f11dca51ee5

Provenance: helper lemma. Supporting algebra for OP-3, arXiv:2610.01024, Section E.1; developed in deep session IN-184. These helpers do not establish a lower bound for arbitrary circuit gate lists.

For a quadratic form on a finite binary coordinate space, vanishing of every fourth difference of twice its binary lift forces the polar matrix to have rank at most two.
-/

theorem binary_quadratic_polar_rank_le_two_of_fourth_difference {n : ℕ}
    (Q : QuadraticForm (ZMod 2) (Fin n → ZMod 2))
    (hfour : ∀ u : Fin 4 → (Fin n → ZMod 2),
      (∑ x : Fin 4 → ZMod 2,
        (-1 : ZMod 8) ^ (∑ i : Fin 4, (x i).val) *
          (2 * ((Q (∑ i : Fin 4, x i • u i)).val : ZMod 8))) = 0) :
    (Matrix.of (fun i j : Fin n =>
      Q.polarBilin (Pi.single i 1) (Pi.single j 1))).rank ≤ 2 := by
  apply binary_quartic_relations_rank_le_two
  intro i j k l
  exact binary_quadratic_polar_quartic_relation Q hfour
    (Pi.single i 1) (Pi.single j 1) (Pi.single k 1) (Pi.single l 1)
