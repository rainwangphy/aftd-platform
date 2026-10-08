import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremProfile
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremCaPref
import AFTD.Kb.Tcs.BooleanAnalysisBoolCube

/-!
# ArrowTheorem.caVotes

Topic: social_choice   Node: 45ba75dba7e1

Provenance: formalization of a published result. Source: TCSlib, `ArrowTheorem.caVotes`. Lean proof by Mina, Allan Li, Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/ArrowTheorem.lean (Apache-2.0); 1 verbatim; compiled here.

Given a profile $p$, the vote vectors $\mathrm{abVotes}(p)$,
$\mathrm{bcVotes}(p)$, $\mathrm{caVotes}(p) \in \{0,1\}^n$ record each
voter's pairwise preference.
-/

set_option maxHeartbeats 800000 in
open scoped BigOperators in
open BooleanAnalysis in
variable {n : ℕ} in
/-- Given a profile, the c-vs-a preference vector. -/
def ArrowTheorem.caVotes (p : Profile n) : BoolCube n := fun i => caPref (p i)
