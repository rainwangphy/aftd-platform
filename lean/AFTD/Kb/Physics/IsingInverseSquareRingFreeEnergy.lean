import AFTD.Prelude
import AFTD.Kb.Physics.IsingRingSpin
import AFTD.Kb.Physics.IsingInverseSquareRingKernel

/-!
# ising_inverse_square_ring_free_energy

Topic: statistical_mechanics   Node: 229d8e8d1d18

Provenance: formalization of a published result. Source: arXiv:2610.39815, Sections 2–4; helper for OP-806.

For natural L and real x and h, the reduced free energy per spin is 1/L times the real logarithm of the sum over functions s from Fin L to Bool of exp(x times the sum over i,j in Fin L with i.val<j.val of the periodized kernel times the real spins at i and j, plus h times the sum over i in Fin L of the real spin at i). True represents spin +1 and false represents -1.
-/

noncomputable def ising_inverse_square_ring_free_energy (L : ℕ) (x h : ℝ) : ℝ := (1 / (L : ℝ)) * Real.log (∑ s : Fin L → Bool,
    Real.exp (x * (∑ i : Fin L, ∑ j : Fin L,
      if i.val < j.val then ising_inverse_square_ring_kernel L i j *
        ising_ring_spin (s i) * ising_ring_spin (s j) else 0) +
      h * (∑ i : Fin L, ising_ring_spin (s i))))
