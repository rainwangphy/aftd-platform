import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremProfile
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremBcVotes
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremCaVotes
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremCorrFunc
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremExpectedProductHelper
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremProfileKernelBcca
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc

/-!
# ArrowTheorem.expected_product_bcca

Topic: social_choice   Node: cb540a7b724f

Provenance: helper lemma. TCSlib, `ArrowTheorem.expected_product_bcca`. Lean proof by Mina, Allan Li, Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/ArrowTheorem.lean (Apache-2.0); 1 verbatim; compiled here.

Expected product of the $bc$ and $ca$ vote vectors. Let $f:\{0,1\}^n\to\bbr$ be a Boolean function, and for each profile
$p:\mathrm{Fin}\,n\to\{0,\dots,5\}$ write $x_{bc}(p),\,x_{ca}(p)\in\{0,1\}^n$ for the
$b$-vs-$c$ and $c$-vs-$a$ vote vectors it induces. Then the average of the product
$f\bigl(x_{bc}(p)\bigr)\,f\bigl(x_{ca}(p)\bigr)$ over all $6^n$ profiles equals the
Fourier correlation function of $f$:
\[
  \Bigl(\tfrac16\Bigr)^{n}\sum_{p} f\bigl(x_{bc}(p)\bigr)\,f\bigl(x_{ca}(p)\bigr)
  \;=\; \mathrm{corr}(f)
  \;=\; \sum_{S\subseteq[n]} \hat f(S)^2\,(-1/3)^{|S|}.
\]
-/

set_option maxHeartbeats 800000 in
open scoped BigOperators in
open BooleanAnalysis in
variable {n : ℕ} in
/-- E[f(bc)·f(ca)] = corrFunc f. -/
lemma ArrowTheorem.expected_product_bcca (f : BooleanFunc n) :
    (1/6 : ℝ)^n * ∑ p : Profile n, f (bcVotes p) * f (caVotes p) = corrFunc f :=
  expected_product_helper f bcVotes caVotes profile_kernel_bcca
