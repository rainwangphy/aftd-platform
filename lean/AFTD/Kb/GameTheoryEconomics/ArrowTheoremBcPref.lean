import AFTD.Prelude

/-!
# ArrowTheorem.bcPref

Topic: social_choice   Node: 739ebbddec22

Provenance: formalization of a published result. Source: TCSlib, `ArrowTheorem.bcPref`. Lean proof by Mina, Allan Li, Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/ArrowTheorem.lean (Apache-2.0); 1 verbatim; compiled here.

$\mathrm{abPref}(k)$, $\mathrm{bcPref}(k)$, $\mathrm{caPref}(k)$ give the
Boolean preference of ordering $k\in\{0,\dots,5\}$ in the $a$-vs-$b$,
$b$-vs-$c$, and $c$-vs-$a$ comparisons, respectively.
-/

set_option maxHeartbeats 800000 in
open scoped BigOperators in
variable {n : ℕ} in
/-- Preference of ordering k in the b-vs-c comparison (false = prefer b). -/
def ArrowTheorem.bcPref : Fin 6 → Bool
  | ⟨0, _⟩ => false  -- a > b > c
  | ⟨1, _⟩ => true   -- a > c > b
  | ⟨2, _⟩ => false  -- b > a > c
  | ⟨3, _⟩ => false  -- b > c > a
  | ⟨4, _⟩ => true   -- c > a > b
  | ⟨5, _⟩ => true   -- c > b > a
