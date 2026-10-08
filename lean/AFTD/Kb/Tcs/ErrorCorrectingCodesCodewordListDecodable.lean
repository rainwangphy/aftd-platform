import AFTD.Prelude
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodeword
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordCode
import AFTD.Kb.Tcs.ErrorCorrectingCodesCodewordHammingBall

/-!
# ErrorCorrectingCodes.Codeword.list_decodable

Topic: information   Node: 5846524cec3d

Provenance: formalization of a published result. Source: TCSlib, `ErrorCorrectingCodes.Codeword.list_decodable`. Lean proof by Allan Li (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/ListDecoding.lean (Apache-2.0); 1 verbatim; compiled here.

A code $C$ is $(\rho,L)$-list-decodable if every Hamming ball of radius
$\lfloor\rho n\rfloor$ contains at most $L$ codewords of $C$.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option linter.unusedSectionVars false in
open Set Filter Asymptotics Finset in
variable {α : Type*} [Fintype α] [Nonempty α] [DecidableEq α] [Field α] in
variable {n k : ℕ} in
/-- A code `C` is `(ρ, L)`-list-decodable if every Hamming ball of radius `⌊ρn⌋` contains at most `L` codewords of `C`. -/
def ErrorCorrectingCodes.Codeword.list_decodable (ρ : ℝ) (hρ₁: 0 ≤ ρ) (hρ₂: ρ ≤ 1) (n L : ℕ) (hL : L ≥ 1) (C : Code n α) : Prop :=
  (∀ y : Codeword n α, (hamming_ball (Nat.floor (ρ*n)) y ∩ C).card ≤ L)
