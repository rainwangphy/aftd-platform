import AFTD.Prelude
import AFTD.Kb.Tcs.CodingTheoryJohnsonBitVec
import AFTD.Kb.Tcs.CodingTheoryJohnsonEuc
import AFTD.Kb.Tcs.CodingTheoryJohnsonOnes
import AFTD.Kb.Tcs.CodingTheoryJohnsonPmOne

/-!
# CodingTheory.Johnson.shifted

Topic: information   Node: dc7c24e102e6

Provenance: formalization of a published result. Source: TCSlib, `CodingTheory.Johnson.shifted`. Lean proof by Allan Li, Frederick Dehmel, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/JohnsonBound.lean (Apache-2.0); 1 verbatim; compiled here.

For a real parameter $\alpha$ and a binary word $x$, the vector
$\hat{x}^\alpha = \mathrm{pmOne}(x) - \alpha \cdot \mathbf{1} \in \mathbb{R}^n$.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators RealInnerProductSpace in
open Finset in
noncomputable def CodingTheory.Johnson.shifted {n : ℕ} (α : ℝ) (x : BitVec n) : Euc n :=
  pmOne x - α • ones
