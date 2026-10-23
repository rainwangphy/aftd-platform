import AFTD.Prelude

/-!
# balanced_blowup_matrix

Topic: graphs   Node: 085681b23c6c

Provenance: formalization of a published result. Source: scout/2610-14100-digraph-laplacian-spectra-the-2005-polygon-conjecture-fails.md:1049

For natural numbers m and d, and an m x m real matrix L on Fin m, balanced_blowup_matrix m d L is the real matrix on Fin m × Fin d defined by D ⊗ I - (1 / d) • (A ⊗ J), where D is the diagonal part of L with entries D i i = L i i and D i j = 0 for i ≠ j, A is the off-diagonal negation of L with entries A i i = 0 and A i j = -L i j for i ≠ j, I is the d x d identity matrix, and J is the d x d all-ones matrix.
-/

/-- The balanced blow-up matrix D (x) I_d - (1/d) A (x) J_d of an m x m matrix L. -/
noncomputable def balanced_blowup_matrix (m d : ℕ) (L : Matrix (Fin m) (Fin m) ℝ) :
    Matrix (Fin m × Fin d) (Fin m × Fin d) ℝ := let D : Matrix (Fin m) (Fin m) ℝ := Matrix.diagonal (fun i => L i i)
   let A : Matrix (Fin m) (Fin m) ℝ := Matrix.of (fun i j => if i = j then 0 else - L i j)
   let I : Matrix (Fin d) (Fin d) ℝ := (1 : Matrix (Fin d) (Fin d) ℝ)
   let J : Matrix (Fin d) (Fin d) ℝ := Matrix.of (fun _ _ => 1)
   Matrix.kronecker D I - (1 / (d : ℝ)) • Matrix.kronecker A J
