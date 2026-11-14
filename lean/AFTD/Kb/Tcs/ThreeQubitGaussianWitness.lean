import AFTD.Prelude

/-!
# three_qubit_gaussian_witness

Topic: quantum   Node: a70b6ce26c52

Provenance: helper lemma.

The normalized three-qubit vector with computational-basis amplitudes (1−i, 1+i, 1+i, −1−i, i, 1, 1, i) divided by sqrt(12).
-/

noncomputable def three_qubit_gaussian_witness : EuclideanSpace ℂ (Fin 3 → Fin 2) := WithLp.toLp 2 (fun u : Fin 3 → Fin 2 =>
    ((Real.sqrt 12 : ℂ)⁻¹) *
      (![![![1 - Complex.I, 1 + Complex.I], ![1 + Complex.I, -1 - Complex.I]],
          ![![Complex.I, 1], ![1, Complex.I]]] : Fin 2 → Fin 2 → Fin 2 → ℂ)
        (u 0) (u 1) (u 2))
