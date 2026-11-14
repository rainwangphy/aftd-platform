import AFTD.Prelude

/-!
# code_bad_projective_set

Topic: information   Node: 7fb373ef43e8

Provenance: formalization of a published result. Source: arXiv:2611.16447 Section 1.1, Lemma 3.8

Given an m by n generator matrix G over a field F and a distance parameter d, the bad projective set consists of all projective points whose codeword under G has Hamming weight at most d - 1.
-/

/-- The set S(G) of projective directions whose codeword under G has Hamming weight at most d - 1. -/
def code_bad_projective_set {F : Type*} [Field F] [DecidableEq F] {m n : ℕ}
    (G : Matrix (Fin m) (Fin n) F) (d : ℕ) : Set (Projectivization F (Fin m → F)) := { p | hammingNorm (Matrix.vecMul p.rep G) ≤ d - 1 }
