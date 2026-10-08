import AFTD.Prelude
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordCode
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordHammingDistance

/-!
# ErrorCorrectingCodes.Codeword.distance

Topic: information   Node: a5c3584c52e9

Provenance: formalization of a published result. Source: TCSlib, `ErrorCorrectingCodes.Codeword.distance`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/Basic.lean (Apache-2.0); 1 verbatim; compiled here.

\texttt{distance C d} holds when $d$ is the minimum Hamming distance of $C$: there
exist distinct codewords at distance exactly $d$, and no two distinct codewords
are closer than $d$.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option linter.unusedSectionVars false in
open Set Filter Asymptotics Finset in
variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α] [Field α] in
variable {n k : ℕ} in
/-- `distance C d` holds when `d` is the minimum Hamming distance of code `C`: there exist two distinct codewords at distance exactly `d`, and no two distinct codewords are closer. -/
def ErrorCorrectingCodes.Codeword.distance (C : Code n α) (d : ℕ) : Prop :=
  (∃ x ∈ C, ∃ y ∈ C, x ≠ y ∧ hamming_distance x y = d) ∧
  (∀ z ∈ C, ∀ w ∈ C, z ≠ w → hamming_distance z w ≥ d)
