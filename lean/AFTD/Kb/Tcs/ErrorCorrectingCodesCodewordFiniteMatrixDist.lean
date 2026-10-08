import AFTD.Prelude
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodeword

/-!
# ErrorCorrectingCodes.Codeword.finite_matrix_dist

Topic: information   Node: 7bf17cb19791

Provenance: helper lemma. TCSlib, `ErrorCorrectingCodes.Codeword.finite_matrix_dist`. Lean proof by Allan Li (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/LinearCodes.lean (Apache-2.0); 1 verbatim; compiled here.

Finiteness of the solution set of a linear matrix equation. Let $\alpha$ be a finite field, and let $n$ and $k$ be natural numbers. Fix a codeword
$v : \mathrm{Fin}\,n \to \alpha$ of length $n$ and a codeword $x : \mathrm{Fin}\,k \to
\alpha$ of length $k$. Then the set of matrices $G \in \alpha^{n \times k}$ satisfying
$Gx = v$ is finite.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option linter.unusedSectionVars false in
open Set Filter Asymptotics Finset in
variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α] [Field α] in
variable {n k m : ℕ} in
/-- The set of matrices `G` such that `G·x = v` is finite. -/
theorem ErrorCorrectingCodes.Codeword.finite_matrix_dist (n k : ℕ) (v : Codeword n α) (x : Codeword k α) :
    Set.Finite { G : Matrix (Fin n) (Fin k) α | Matrix.mulVec G x = v } := by {
  have dist_subset :
    { G : Matrix (Fin n) (Fin k) α | Matrix.mulVec G x = v } ⊆
    (Set.univ : Set (Matrix (Fin n) (Fin k) α)) := by
      intro G _
      trivial

  have matrices_fintype : Finite ↑{G | Matrix.mulVec G x = v} := by
    exact Finite.Set.subset (Set.univ : Set (Matrix (Fin n) (Fin k) α)) dist_subset

  exact (Set.finite_coe_iff.mp matrices_fintype)
}
