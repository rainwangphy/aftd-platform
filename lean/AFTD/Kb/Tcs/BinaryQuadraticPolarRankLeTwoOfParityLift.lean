import AFTD.Prelude
import AFTD.Kb.Tcs.BinaryQuadraticPolarRankLeTwoOfFourthDifference
import AFTD.Kb.Tcs.ParityPhaseFourthDifference

/-!
# binary_quadratic_polar_rank_le_two_of_parity_lift

Topic: quantum   Node: a1489aa3cf17

Provenance: helper lemma. Supporting algebra for OP-3, arXiv:2610.01024, Section E.1; developed in deep session IN-184. These helpers do not establish a lower bound for arbitrary circuit gate lists.

If twice the binary lift of a quadratic form is a finite parity-phase polynomial modulo eight, its polar matrix has rank at most two.
-/

theorem binary_quadratic_polar_rank_le_two_of_parity_lift {n : ℕ} {ι : Type*}
    [Fintype ι]
    (Q : QuadraticForm (ZMod 2) (Fin n → ZMod 2))
    (c : ι → ZMod 8) (L : ι → (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2)
    (hrepr : ∀ v, 2 * ((Q v).val : ZMod 8) =
      ∑ j : ι, c j * ((L j v).val : ZMod 8)) :
    (Matrix.of (fun i j : Fin n =>
      Q.polarBilin (Pi.single i 1) (Pi.single j 1))).rank ≤ 2 := by
  apply binary_quadratic_polar_rank_le_two_of_fourth_difference Q
  intro u
  simp_rw [hrepr]
  exact parity_phase_fourth_difference c L u
