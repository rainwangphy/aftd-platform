import AFTD.Prelude

/-!
# three_qubit_regular_ghz_witness

Topic: quantum   Node: cb5ceb027495

Provenance: helper lemma.

The normalized Gaussian vector with amplitudes (−8,−4+8i,−2−4i,−1+i,−7−7i,−8+4i,4+2i,6i) divided by 20.
-/

noncomputable def three_qubit_regular_ghz_witness : EuclideanSpace ℂ (Fin 3 → Fin 2) := WithLp.toLp 2 (fun u : Fin 3 → Fin 2 =>
    ((20 : ℂ)⁻¹) *
      (![![![-8, -4 + 8*Complex.I], ![-2 - 4*Complex.I, -1 + Complex.I]],
          ![![-7 - 7*Complex.I, -8 + 4*Complex.I], ![4 + 2*Complex.I, 6*Complex.I]]] : Fin 2 → Fin 2 → Fin 2 → ℂ)
        (u 0) (u 1) (u 2))
