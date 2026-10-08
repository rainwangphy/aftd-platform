import AFTD.Prelude
import AFTD.Kb.Tcs.CodingTheoryJohnsonOnes

/-!
# CodingTheory.Johnson.ones_apply

Topic: information   Node: 4602ef631338

Provenance: helper lemma. TCSlib, `CodingTheory.Johnson.ones_apply`. Lean proof by Allan Li, Frederick Dehmel, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/JohnsonBound.lean (Apache-2.0); 1 verbatim; compiled here.

Coordinates of the all-ones vector. Let $\mathbf{1} \in \bbr^n$ be the all-ones vector. Then for every index $i \in \{1,
\dots, n\}$, the $i$-th coordinate satisfies $\mathbf{1}_i = 1$.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators RealInnerProductSpace in
open Finset in
@[simp] lemma CodingTheory.Johnson.ones_apply {n : ℕ} (i : Fin n) : ones (n := n) i = (1 : ℝ) := by simp [ones]
