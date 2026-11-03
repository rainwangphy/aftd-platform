import AFTD.Prelude
import AFTD.Kb.Tcs.DualMelasJointPatternProb
import AFTD.Kb.Tcs.DualMelasPatternCountLe
import AFTD.Kb.Tcs.CyclicRotateLeft
import AFTD.Kb.Tcs.DualMelasPatternCount

/-!
# dual_melas_joint_pattern_prob_eq_zero_of_ge

Topic: information   Node: 6b79108303eb

Provenance: helper lemma. step towards dual_melas_adjacent_cyclic_patterns_bivariate_poisson_limit

For any field F finite-dimensional over ZMod 2, natural number k, elements α, c ∈ F, and natural numbers a, b such that 2^k ≤ a or 2^k ≤ b, dual_melas_joint_pattern_prob k α c a b = 0.
-/

/-- Joint pattern probability vanishes when either count is at least 2^k. -/
theorem dual_melas_joint_pattern_prob_eq_zero_of_ge
    {F : Type*} [Field F] [Algebra (ZMod 2) F] [FiniteDimensional (ZMod 2) F]
    (k : ℕ) (α c : F) (a b : ℕ) (h : 2 ^ k ≤ a ∨ 2 ^ k ≤ b) :
    dual_melas_joint_pattern_prob k α c a b = 0 := by
  unfold dual_melas_joint_pattern_prob
  have h_empty : Finset.filter (fun (w : Fin k → ZMod 2) =>
      dual_melas_pattern_count k α c w = a ∧
      dual_melas_pattern_count k α c (cyclic_rotate_left k w) = b) Finset.univ = ∅ := by
    rw [Finset.filter_eq_empty_iff]
    intro w _
    have h1 := dual_melas_pattern_count_le k α c w
    have h2 := dual_melas_pattern_count_le k α c (cyclic_rotate_left k w)
    have hk : 0 < 2 ^ k := Nat.two_pow_pos k
    intro ⟨hwa, hwb⟩
    rcases h with ha | hb
    · omega
    · omega
  rw [h_empty]
  simp
