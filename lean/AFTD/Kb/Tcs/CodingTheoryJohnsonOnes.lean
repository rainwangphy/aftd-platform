import AFTD.Prelude
import AFTD.Kb.Tcs.CodingTheoryJohnsonEuc

/-!
# CodingTheory.Johnson.ones

Topic: information   Node: 1a518810bac2

Provenance: formalization of a published result. Source: TCSlib, `CodingTheory.Johnson.ones`. Lean proof by Allan Li, Frederick Dehmel, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/JohnsonBound.lean (Apache-2.0); 1 verbatim; compiled here.

The vector in $\mathbb{R}^n$ all of whose coordinates equal $1$.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators RealInnerProductSpace in
open Finset in
noncomputable def CodingTheory.Johnson.ones {n : ℕ} : Euc n :=
  WithLp.toLp 2 (fun _ => (1 : ℝ))
