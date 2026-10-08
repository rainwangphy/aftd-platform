import AFTD.Prelude

/-!
# ArrowTheorem.abPref

Topic: social_choice   Node: a6c8cba0ca8d

Provenance: formalization of a published result. Source: TCSlib, `ArrowTheorem.abPref`. Lean proof by Mina, Allan Li, Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/ArrowTheorem.lean (Apache-2.0); 1 verbatim; compiled here.

$\mathrm{abPref}(k)$, $\mathrm{bcPref}(k)$, $\mathrm{caPref}(k)$ give the
Boolean preference of ordering $k\in\{0,\dots,5\}$ in the $a$-vs-$b$,
$b$-vs-$c$, and $c$-vs-$a$ comparisons, respectively.
-/

set_option maxHeartbeats 800000 in
open scoped BigOperators in
variable {n : ℕ} in
/-- Preference of ordering k in the a-vs-b comparison (false = prefer a). -/
def ArrowTheorem.abPref : Fin 6 → Bool
  | ⟨0, _⟩ => false  -- a > b > c
  | ⟨1, _⟩ => false  -- a > c > b
  | ⟨2, _⟩ => true   -- b > a > c
  | ⟨3, _⟩ => true   -- b > c > a
  | ⟨4, _⟩ => false  -- c > a > b
  | ⟨5, _⟩ => true   -- c > b > a
