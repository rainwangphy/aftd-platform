import AFTD.Prelude
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodeword
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordFiniteMatrixDist

/-!
# ErrorCorrectingCodes.Codeword.matrix_dist

Topic: information   Node: 6c6f7fecebad

Provenance: formalization of a published result. Source: TCSlib, `ErrorCorrectingCodes.Codeword.matrix_dist`. Lean proof by Allan Li (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/LinearCodes.lean (Apache-2.0); 1 verbatim; compiled here.

$\mu_x(v)$ is the fraction of $n\times k$ matrices $G$ satisfying $Gx=v$.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option linter.unusedSectionVars false in
open Set Filter Asymptotics Finset in
variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α] [Field α] in
variable {n k m : ℕ} in
/-- The distribution on `αⁿ` induced by applying a uniformly random `n×k` matrix to `x`: `matrix_dist n k x v = |{G | G·x = v}| / |α|^(n·k)`. -/
noncomputable def ErrorCorrectingCodes.Codeword.matrix_dist (n k : ℕ) (x : Codeword k α) : (Codeword n α) → ℝ :=
  fun v => (Set.Finite.toFinset (finite_matrix_dist n k v x)).card / ((Fintype.card α) ^ (n * k))
