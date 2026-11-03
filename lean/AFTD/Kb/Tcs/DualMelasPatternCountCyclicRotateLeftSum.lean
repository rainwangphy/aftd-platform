import AFTD.Prelude
import AFTD.Kb.Tcs.DualMelasPatternCountSum
import AFTD.Kb.Tcs.CyclicRotateLeftBijective
import AFTD.Kb.Tcs.DualMelasPatternCount
import AFTD.Kb.Tcs.CyclicRotateLeft

/-!
# dual_melas_pattern_count_cyclic_rotate_left_sum

Topic: information   Node: 5ec1482cb718

Provenance: helper lemma. step towards dual_melas_adjacent_cyclic_patterns_bivariate_poisson_limit

For any field F finite-dimensional over ZMod 2, positive natural number k, and elements α, c ∈ F, the sum over all words w : Fin k → ZMod 2 of dual_melas_pattern_count k α c (cyclic_rotate_left k w) equals 2^k - 1.
-/

/-- Sum of rotated pattern counts over all binary words equals 2^k - 1. -/
theorem dual_melas_pattern_count_cyclic_rotate_left_sum
    {F : Type*} [Field F] [Algebra (ZMod 2) F] [FiniteDimensional (ZMod 2) F]
    (k : ℕ) (hk : 0 < k) (α c : F) :
    ∑ w : Fin k → ZMod 2, dual_melas_pattern_count k α c (cyclic_rotate_left k w) = 2 ^ k - 1 := by
  let e := Equiv.ofBijective (cyclic_rotate_left (α := ZMod 2) k)
    (cyclic_rotate_left_bijective k hk (ZMod 2))
  have hsum : ∑ w : Fin k → ZMod 2, dual_melas_pattern_count k α c (cyclic_rotate_left k w)
      = ∑ w : Fin k → ZMod 2, dual_melas_pattern_count k α c w := by
    rw [← Equiv.sum_comp e (fun w => dual_melas_pattern_count k α c w)]
    rfl
  rw [hsum, dual_melas_pattern_count_sum k α c]
