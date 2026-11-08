import AFTD.Prelude

/-!
# stabilizedSubspace

Topic: quantum   Node: 348d239768dd

Provenance: formalization of a published result. Source: arXiv:2610.37807 Definition 4

Given a natural number $n$ and a subgroup $S \le (\mathrm{Matrix}\,(\mathrm{Fin}\,(2^n))\,(\mathrm{Fin}\,(2^n))\,\mathbb{C})^\times$, the stabilized subspace $\operatorname{stab}(S)$ is the $\mathbb{C}$-submodule of $\mathrm{Fin}\,(2^n) \to \mathbb{C}$ consisting of vectors $v$ fixed by every matrix in $S$, i.e., $s v = v$ for all $s \in S$.
-/

/-- The stabilized subspace stab(S) of a subgroup of (Matrix (Fin (2^n)) (Fin (2^n)) ℂ)ˣ. -/
def stabilizedSubspace (n : ℕ) (S : Subgroup (Matrix (Fin (2^n)) (Fin (2^n)) ℂ)ˣ) :
    Submodule ℂ (Fin (2^n) → ℂ) where
  carrier := {v | ∀ s ∈ S, Matrix.mulVec (s : Matrix (Fin (2^n)) (Fin (2^n)) ℂ) v = v}
  add_mem' {v w} hv hw s hs := by
    show Matrix.mulVec (s : Matrix (Fin (2^n)) (Fin (2^n)) ℂ) (v + w) = v + w
    rw [Matrix.mulVec_add, hv s hs, hw s hs]
  zero_mem' s hs := by
    show Matrix.mulVec (s : Matrix (Fin (2^n)) (Fin (2^n)) ℂ) 0 = 0
    rw [Matrix.mulVec_zero]
  smul_mem' c v hv s hs := by
    show Matrix.mulVec (s : Matrix (Fin (2^n)) (Fin (2^n)) ℂ) (c • v) = c • v
    rw [Matrix.mulVec_smul, hv s hs]
