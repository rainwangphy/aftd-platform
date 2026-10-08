import AFTD.Prelude

/-!
# ArrowTheorem.caPref

Topic: social_choice   Node: 7c7538ab7cbc

Provenance: formalization of a published result. Source: TCSlib, `ArrowTheorem.caPref`. Lean proof by Mina, Allan Li, Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/ArrowTheorem.lean (Apache-2.0); 1 verbatim; compiled here.

$\mathrm{abPref}(k)$, $\mathrm{bcPref}(k)$, $\mathrm{caPref}(k)$ give the
Boolean preference of ordering $k\in\{0,\dots,5\}$ in the $a$-vs-$b$,
$b$-vs-$c$, and $c$-vs-$a$ comparisons, respectively.
-/

set_option maxHeartbeats 800000 in
open scoped BigOperators in
variable {n : ℕ} in
/-- Preference of ordering k in the c-vs-a comparison (false = prefer c). -/
def ArrowTheorem.caPref : Fin 6 → Bool
  | ⟨0, _⟩ => true   -- a > b > c: prefer a, so in ca: prefer a = true
  | ⟨1, _⟩ => true   -- a > c > b
  | ⟨2, _⟩ => true   -- b > a > c
  | ⟨3, _⟩ => false  -- b > c > a: prefer c
  | ⟨4, _⟩ => false  -- c > a > b: prefer c
  | ⟨5, _⟩ => false  -- c > b > a: prefer c
