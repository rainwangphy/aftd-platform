import AFTD.Prelude

/-!
# pauli_bloch_matrix

Topic: quantum   Node: 099d24c2b54e

Provenance: helper lemma. arXiv:2611.19367v1, Lemma 3, Eqs. (29)–(31), for the Pauli alignment construction.

The Hermitian two by two Pauli matrix corresponding to a real three-dimensional Bloch vector.
-/

open scoped Matrix

noncomputable def pauli_bloch_matrix (b : Fin 3 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(b 2 : ℂ), (b 0 : ℂ) - Complex.I * (b 1 : ℂ);
     (b 0 : ℂ) + Complex.I * (b 1 : ℂ), -(b 2 : ℂ)]
