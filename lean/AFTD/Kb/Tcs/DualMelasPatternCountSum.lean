import AFTD.Prelude
import AFTD.Kb.Tcs.DualMelasPatternCount
import AFTD.Kb.Tcs.DualMelasWindow

/-!
# dual_melas_pattern_count_sum

Topic: information   Node: 986cd21c9058

Provenance: helper lemma. scout/2610-38017-on-the-b-symbol-weight-distribution-of-dual-melas-codes-and.md:1189

For any field F finite-dimensional over ZMod 2, natural number k, and elements α, c ∈ F, the sum over all binary words w : Fin k → ZMod 2 of dual_melas_pattern_count k α c w is equal to 2 ^ k - 1.
-/

/-- The sum of pattern counts N_w over all 2^k words of length k equals the period length 2^k - 1. -/
theorem dual_melas_pattern_count_sum {F : Type*} [Field F] [Algebra (ZMod 2) F] [FiniteDimensional (ZMod 2) F] (k : ℕ) (α c : F) : ∑ w : Fin k → ZMod 2, dual_melas_pattern_count k α c w = 2 ^ k - 1 := by
  have h := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (Fin (2 ^ k - 1))))
    (t := (Finset.univ : Finset (Fin k → ZMod 2)))
    (f := fun i : Fin (2 ^ k - 1) => dual_melas_window k α c i.val)
    (fun x _ => Finset.mem_univ _)
  simp only [Finset.card_univ, Fintype.card_fin] at h
  rw [h]
  rfl
