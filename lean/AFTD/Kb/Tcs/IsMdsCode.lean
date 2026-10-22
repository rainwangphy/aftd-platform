import AFTD.Prelude

/-!
# is_mds_code

Topic: information   Node: dad27d0fc9d4

Provenance: formalization of a published result. Source: arXiv:2610.28047 Section 2.2

For a finite field F, natural numbers n and k, a subspace C of Fin n → F has dimension k (Module.finrank F C = k) and is an MDS code if every nonzero vector v in C satisfies n - k + 1 ≤ hammingNorm v.
-/

/-- A linear code of dimension k is MDS if every nonzero codeword has Hamming weight at least n - k + 1. -/
def is_mds_code {F : Type*} [Field F] [Fintype F] [DecidableEq F] (n k : ℕ) (C : Subspace F (Fin n → F)) : Prop := Module.finrank F C = k ∧ ∀ v ∈ C, v ≠ 0 → n - k + 1 ≤ hammingNorm v
