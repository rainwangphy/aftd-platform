import AFTD.Prelude
import AFTD.Kb.Tcs.DualMelasPatternCount
import AFTD.Kb.Tcs.CyclicRotateLeft

/-!
# dual_melas_joint_pattern_prob

Topic: information   Node: 05d94f7f2004

Provenance: formalization of a published result. Source: scout/2610-38017-on-the-b-symbol-weight-distribution-of-dual-melas-codes-and.md:1043

For a field F finite-dimensional over ZMod 2, natural number k, elements α, c : F, and natural numbers a, b : ℕ, dual_melas_joint_pattern_prob k α c a b is the proportion of words w : Fin k → ZMod 2 satisfying dual_melas_pattern_count k α c w = a and dual_melas_pattern_count k α c (cyclic_rotate_left k w) = b, divided by 2^k.
-/

/-- The empirical joint probability that N_W = a and N_{RW} = b for uniform random W in (Fin k → ZMod 2). -/
noncomputable def dual_melas_joint_pattern_prob {F : Type*} [Field F] [Algebra (ZMod 2) F] [FiniteDimensional (ZMod 2) F] (k : ℕ) (α c : F) (a b : ℕ) : ℝ := (Finset.card (Finset.filter (fun (w : Fin k → ZMod 2) => dual_melas_pattern_count k α c w = a ∧ dual_melas_pattern_count k α c (cyclic_rotate_left k w) = b) Finset.univ) : ℝ) / (2 ^ k : ℝ)
