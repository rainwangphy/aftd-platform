import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremProfile
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremAbVotes
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremBcVotes
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremCaVotes
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc

/-!
# ArrowTheorem.acyclic

Topic: social_choice   Node: 11f93088923b

Provenance: formalization of a published result. Source: TCSlib, `ArrowTheorem.acyclic`. Lean proof by Mina, Allan Li, Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/ArrowTheorem.lean (Apache-2.0); 1 verbatim; compiled here.

A social welfare function $f$ is \emph{acyclic} if no profile of transitive
voter orderings produces a Condorcet cycle in society's preferences.
A cycle occurs when
$f(\mathrm{abVotes}(p)) = f(\mathrm{bcVotes}(p)) = f(\mathrm{caVotes}(p)) = 1$
(the cycle $a>b>c>a$) or all equal $-1$ (the reverse cycle).
-/

set_option maxHeartbeats 800000 in
open scoped BigOperators in
open BooleanAnalysis in
variable {n : ℕ} in
/-- A social welfare function `f` is **acyclic** if no profile of transitive voter orderings produces a Condorcet cycle in society's preferences. A Condorcet cycle occurs when f(ab) = f(bc) = f(ca) = 1 (society prefers a to b, b to c, and c to a — a cycle a>b>c>a) or f(ab) = f(bc) = f(ca) = -1 (the reverse cycle). **Source:** [OD14, Ch. 2]. -/
def ArrowTheorem.acyclic (f : BooleanFunc n) : Prop :=
  ∀ p : Profile n,
    ¬ (f (abVotes p) = 1 ∧ f (bcVotes p) = 1 ∧ f (caVotes p) = 1) ∧
    ¬ (f (abVotes p) = -1 ∧ f (bcVotes p) = -1 ∧ f (caVotes p) = -1)
