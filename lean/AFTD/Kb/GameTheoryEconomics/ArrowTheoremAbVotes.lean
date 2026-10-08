import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremProfile
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremAbPref
import AFTD.Kb.Tcs.BooleanAnalysisBoolCube

/-!
# ArrowTheorem.abVotes

Topic: social_choice   Node: 4a40d7320b2c

Provenance: formalization of a published result. Source: TCSlib, `ArrowTheorem.abVotes`. Lean proof by Mina, Allan Li, Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/ArrowTheorem.lean (Apache-2.0); 1 verbatim; compiled here.

Given a profile $p$, the vote vectors $\mathrm{abVotes}(p)$,
$\mathrm{bcVotes}(p)$, $\mathrm{caVotes}(p) \in \{0,1\}^n$ record each
voter's pairwise preference.
-/

set_option maxHeartbeats 800000 in
open scoped BigOperators in
open BooleanAnalysis in
variable {n : ℕ} in
/-- Given a profile, the a-vs-b preference vector of all n voters. -/
def ArrowTheorem.abVotes (p : Profile n) : BoolCube n := fun i => abPref (p i)
