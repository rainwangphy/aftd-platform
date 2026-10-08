import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremProfile
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremAbVotes
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremBcVotes
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremCorrFunc
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremExpectedProductHelper
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremProfileInnerProductKernel
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc

/-!
# ArrowTheorem.expected_product_eq_corrFunc

Topic: social_choice   Node: 73299ea2d2a5

Provenance: helper lemma. TCSlib, `ArrowTheorem.expected_product_eq_corrFunc`. Lean proof by Mina, Allan Li, Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/ArrowTheorem.lean (Apache-2.0); 1 verbatim; compiled here.

Expected pairwise vote product equals the Fourier correlation function. Let $f:\{0,1\}^n\to\bbr$ be a Boolean function. Suppose each of the $n$ voters chooses,
independently and uniformly, one of the six strict orderings of three candidates
$a,b,c$; for such a profile $p$ write $x_p\in\{0,1\}^n$ for the vector whose $i$-th
entry records voter $i$'s preference in the $a$-versus-$b$ comparison, and
$y_p\in\{0,1\}^n$ for the vector recording each voter's preference in the $b$-versus-$c$
comparison. Then, averaging the product of the values of $f$ on these two vectors over
all $6^n$ profiles,
\[
  \frac{1}{6^{\,n}}\sum_{p}\, f(x_p)\,f(y_p)
  \;=\; \sum_{S\subseteq[n]} \hat f(S)^2\,(-1/3)^{|S|},
\]
where $\hat f(S)$ denotes the Fourier--Walsh coefficient of $f$ at frequency $S$.
-/

set_option maxHeartbeats 800000 in
open scoped BigOperators in
open BooleanAnalysis in
variable {n : ℕ} in
/-- E[f(ab)·f(bc)] = corrFunc f. -/
lemma ArrowTheorem.expected_product_eq_corrFunc (f : BooleanFunc n) :
    (1/6 : ℝ)^n * ∑ p : Profile n, f (abVotes p) * f (bcVotes p) = corrFunc f :=
  expected_product_helper f abVotes bcVotes profile_inner_product_kernel
