import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremProfile
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremAbVotes
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremCaVotes
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremCorrFunc
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremExpectedProductHelper
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremProfileKernelAbca
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc

/-!
# ArrowTheorem.expected_product_abca

Topic: social_choice   Node: 4a835c7b348d

Provenance: helper lemma. TCSlib, `ArrowTheorem.expected_product_abca`. Lean proof by Mina, Allan Li, Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/ArrowTheorem.lean (Apache-2.0); 1 verbatim; compiled here.

Expected product of the $ab$ and $ca$ votes. Let $f:\{0,1\}^n\to\bbr$ be a Boolean function. For a profile $p$ that assigns each of
the $n$ voters one of the six strict orderings of the three alternatives $a,b,c$, let
$x^{ab}(p)\in\{0,1\}^n$ record each voter's preference in the $a$-vs-$b$ comparison and
let $x^{ca}(p)\in\{0,1\}^n$ record each voter's preference in the $c$-vs-$a$ comparison.
Averaging uniformly over all $6^n$ profiles, the expected product of $f$ at these two
vote vectors equals the Fourier correlation function of $f$:
\[
  \Bigl(\tfrac{1}{6}\Bigr)^{n}\sum_{p} f\bigl(x^{ab}(p)\bigr)\,f\bigl(x^{ca}(p)\bigr)
  \;=\; \sum_{S\subseteq[n]} \hat f(S)^{2}\,(-1/3)^{|S|}.
\]
-/

set_option maxHeartbeats 800000 in
open scoped BigOperators in
open BooleanAnalysis in
variable {n : ℕ} in
/-- E[f(ab)·f(ca)] = corrFunc f. -/
lemma ArrowTheorem.expected_product_abca (f : BooleanFunc n) :
    (1/6 : ℝ)^n * ∑ p : Profile n, f (abVotes p) * f (caVotes p) = corrFunc f :=
  expected_product_helper f abVotes caVotes profile_kernel_abca
