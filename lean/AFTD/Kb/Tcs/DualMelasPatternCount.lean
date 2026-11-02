import AFTD.Prelude
import AFTD.Kb.Tcs.DualMelasWindow

/-!
# dual_melas_pattern_count

Topic: information   Node: e228526e37b4

Provenance: formalization of a published result. Source: scout/2610-38017-on-the-b-symbol-weight-distribution-of-dual-melas-codes-and.md:1040

For a field F finite-dimensional over ZMod 2, natural number k, elements α, c : F, and word w : Fin k → ZMod 2, dual_melas_pattern_count k α c w is the number of indices i : Fin (2 ^ k - 1) such that dual_melas_window k α c i.val = w.
-/

/-- The number of cyclic occurrences of pattern w in one period of length 2^k - 1 of the dual Melas sequence. -/
noncomputable def dual_melas_pattern_count {F : Type*} [Field F] [Algebra (ZMod 2) F] [FiniteDimensional (ZMod 2) F] (k : ℕ) (α c : F) (w : Fin k → ZMod 2) : ℕ := Finset.card (Finset.filter (fun (i : Fin (2 ^ k - 1)) => dual_melas_window k α c i.val = w) Finset.univ)
