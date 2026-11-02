import AFTD.Prelude
import AFTD.Kb.Physics.IsingInverseSquareRingFreeEnergy
import AFTD.Kb.Physics.IsingInverseSquareRingKernel
import AFTD.Kb.Physics.IsingRingSpin

/-!
# ising_inverse_square_ring_partition

Topic: statistical_mechanics   Node: 7474f69af871

Provenance: helper lemma. step towards ising_inverse_square_bulk_field_polynomials_real_rooted

The finite-ring partition function at coupling x and field h is the sum over all spin configurations of exp of the interaction energy times x plus the field energy times h.
-/

/-- The finite-ring Ising partition function whose log, divided by L, is the reduced free energy. -/
noncomputable def ising_inverse_square_ring_partition (L : ℕ) (x h : ℝ) : ℝ := ∑ s : Fin L → Bool,
    Real.exp (x * (∑ i : Fin L, ∑ j : Fin L,
      if i.val < j.val then ising_inverse_square_ring_kernel L i j *
        ising_ring_spin (s i) * ising_ring_spin (s j) else 0) +
      h * (∑ i : Fin L, ising_ring_spin (s i)))
