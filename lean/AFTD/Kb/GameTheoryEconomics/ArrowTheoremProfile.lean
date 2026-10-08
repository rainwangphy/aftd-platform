import AFTD.Prelude

/-!
# ArrowTheorem.Profile

Topic: social_choice   Node: 7f0c2fa4aa40

Provenance: formalization of a published result. Source: TCSlib, `ArrowTheorem.Profile`. Lean proof by Mina, Allan Li, Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/ArrowTheorem.lean (Apache-2.0); 1 verbatim; compiled here.

A \emph{profile} assigns each of the $n$ voters one of the 6 orderings:
$p : \mathrm{Fin}\,n \to \mathrm{Fin}\,6$.
-/

set_option maxHeartbeats 800000 in
open scoped BigOperators in
variable {n : ℕ} in
/-- A **profile** assigns each of the n voters one of the 6 orderings. -/
abbrev ArrowTheorem.Profile (n : ℕ) := Fin n → Fin 6
