import AFTD.Prelude

/-!
# symmetric_game_regret

Topic: equilibria   Node: c91c1bcc2050

Provenance: formalization of a published result. Source: arXiv:2610.25524 Section 1.1

For a positive natural number n, an n-by-n matrix A over ℝ, and a strategy p in `stdSimplex ℝ (Fin n)`, the symmetric game regret `symmetric_game_regret A p` is `Finset.univ.sup' Finset.univ_nonempty (fun i => Matrix.mulVec A p.val i) - dotProduct p.val (Matrix.mulVec A p.val)`.
-/

/-- Symmetric game regret of a strategy p: max_i e_iᵀ A p - pᵀ A p. -/
def symmetric_game_regret {n : ℕ} [NeZero n] (A : Matrix (Fin n) (Fin n) ℝ) (p : stdSimplex ℝ (Fin n)) : ℝ := (Finset.univ.sup' Finset.univ_nonempty (fun i => Matrix.mulVec A p.val i)) - dotProduct p.val (Matrix.mulVec A p.val)
