import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremProfile
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremBcPref
import AFTD.Kb.Tcs.BooleanAnalysisBoolCube

/-!
# ArrowTheorem.bcVotes

Topic: social_choice   Node: 5f50d5925bfb

Provenance: formalization of a published result. Source: TCSlib, `ArrowTheorem.bcVotes`. Lean proof by Mina, Allan Li, Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/ArrowTheorem.lean (Apache-2.0); 1 verbatim; compiled here.

Given a profile $p$, the vote vectors $\mathrm{abVotes}(p)$,
$\mathrm{bcVotes}(p)$, $\mathrm{caVotes}(p) \in \{0,1\}^n$ record each
voter's pairwise preference.
-/

set_option maxHeartbeats 800000 in
open scoped BigOperators in
open BooleanAnalysis in
variable {n : ℕ} in
/-- Given a profile, the b-vs-c preference vector. -/
def ArrowTheorem.bcVotes (p : Profile n) : BoolCube n := fun i => bcPref (p i)
