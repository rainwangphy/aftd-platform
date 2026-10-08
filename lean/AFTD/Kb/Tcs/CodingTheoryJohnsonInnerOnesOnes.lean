import AFTD.Prelude
import AFTD.Kb.Tcs.CodingTheoryJohnsonOnes

/-!
# CodingTheory.Johnson.inner_ones_ones

Topic: information   Node: 11c935df4663

Provenance: helper lemma. TCSlib, `CodingTheory.Johnson.inner_ones_ones`. Lean proof by Allan Li, Frederick Dehmel, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/JohnsonBound.lean (Apache-2.0); 1 verbatim; compiled here.

Squared norm of the all-ones vector. Let $\mathbf{1} \in \bbr^n$ denote the vector all of whose coordinates equal $1$. Then,
with respect to the standard $\ell^2$ inner product, $\langle \mathbf{1}, \mathbf{1}
\rangle = n$.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators RealInnerProductSpace in
open Finset in
lemma CodingTheory.Johnson.inner_ones_ones {n : ℕ} :
    ⟪ones (n := n), ones (n := n)⟫_[ℝ] = (n : ℝ) := by
  simp [RCLike.wInner, ones]
