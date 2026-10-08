import AFTD.Prelude
import AFTD.Kb.Tcs.CodingTheoryJohnsonEuc

/-!
# CodingTheory.Johnson.normalize

Topic: information   Node: dd905f208113

Provenance: formalization of a published result. Source: TCSlib, `CodingTheory.Johnson.normalize`. Lean proof by Allan Li, Frederick Dehmel, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/JohnsonBound.lean (Apache-2.0); 1 verbatim; compiled here.

The rescaling $u \mapsto \norm{u}^{-1} \cdot u$ of a vector of $\mathbb{R}^n$.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators RealInnerProductSpace in
open Finset in
noncomputable def CodingTheory.Johnson.normalize {n : ℕ} (u : Euc n) : Euc n :=
  (‖u‖)⁻¹ • u
