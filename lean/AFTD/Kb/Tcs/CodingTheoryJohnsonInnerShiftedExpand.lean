import AFTD.Prelude
import AFTD.Kb.Tcs.CodingTheoryJohnsonBitVec
import AFTD.Kb.Tcs.CodingTheoryJohnsonOnes
import AFTD.Kb.Tcs.CodingTheoryJohnsonPmOne
import AFTD.Kb.Tcs.CodingTheoryJohnsonShifted

/-!
# CodingTheory.Johnson.inner_shifted_expand

Topic: information   Node: 006f9c926f9a

Provenance: helper lemma. TCSlib, `CodingTheory.Johnson.inner_shifted_expand`. Lean proof by Allan Li, Frederick Dehmel, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/JohnsonBound.lean (Apache-2.0); 1 verbatim; compiled here.

Bilinear expansion of the shifted inner product. Let $\alpha \in \bbr$, let $x, y$ be binary words of length $n$, and write $\mathbf{1}$
for the all-ones vector in $\bbr^n$ and $s(x), s(y) \in \bbr^n$ for the $\pm 1$
embeddings of $x$ and $y$ (with $i$-th coordinate $-1$ where the corresponding bit is
true and $+1$ otherwise). Form the shifted vectors $\hat{x}^\alpha = s(x) - \alpha
\mathbf{1}$ and $\hat{y}^\alpha = s(y) - \alpha \mathbf{1}$. Then their Euclidean inner
product expands as
\[
\langle \hat{x}^\alpha,\, \hat{y}^\alpha \rangle
= \langle s(x),\, s(y) \rangle
- \alpha\,\langle s(x),\, \mathbf{1} \rangle
- \alpha\,\langle s(y),\, \mathbf{1} \rangle
+ \alpha^2\,\langle \mathbf{1},\, \mathbf{1} \rangle.
\]
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators RealInnerProductSpace in
open Finset in
lemma CodingTheory.Johnson.inner_shifted_expand {n : ℕ} (α : ℝ) (x y : BitVec n) :
    ⟪shifted α x, shifted α y⟫_[ℝ]
      = ⟪pmOne x, pmOne y⟫_[ℝ]
        - α * ⟪pmOne x, ones (n := n)⟫_[ℝ]
        - α * ⟪pmOne y, ones (n := n)⟫_[ℝ]
        + α^2 * ⟪ones (n := n), ones (n := n)⟫_[ℝ] := by
  unfold shifted
  simp [RCLike.wInner];
  simp [mul_sub, sub_mul, Finset.sum_sub_distrib, Finset.mul_sum _ _ _, pow_two];
  simp [mul_comm, mul_assoc, sub_eq_add_neg]
  ring
