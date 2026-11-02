import AFTD.Prelude
import AFTD.Kb.Tcs.DualMelasSeq

/-!
# dual_melas_window

Topic: information   Node: 96df40d8d5f3

Provenance: formalization of a published result. Source: scout/2610-38017-on-the-b-symbol-weight-distribution-of-dual-melas-codes-and.md:1043

For a field F finite-dimensional over ZMod 2, natural number k, elements α, c : F, and index i : ℕ, dual_melas_window k α c i is the word of length k mapping j : Fin k to dual_melas_seq α c ((i + j.val) % (2 ^ k - 1)).
-/

/-- The length-k window starting at index i cyclically mod 2^k - 1 in the dual Melas sequence. -/
noncomputable def dual_melas_window {F : Type*} [Field F] [Algebra (ZMod 2) F] [FiniteDimensional (ZMod 2) F] (k : ℕ) (α c : F) (i : ℕ) : Fin k → ZMod 2 := fun j => dual_melas_seq α c ((i + j.val) % (2 ^ k - 1))
