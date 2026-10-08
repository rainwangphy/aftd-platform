import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremProfile
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremBcVotes
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremCaVotes
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremSumBcPrefCaPref
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremProfileKernelGen
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremSumBcPrefSign
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremSumCaPrefSign
import AFTD.Kb.Tcs.BooleanAnalysisChiS

/-!
# ArrowTheorem.profile_kernel_bcca

Topic: social_choice   Node: 8e58b60437e5

Provenance: helper lemma. TCSlib, `ArrowTheorem.profile_kernel_bcca`. Lean proof by Mina, Allan Li, Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/ArrowTheorem.lean (Apache-2.0); 1 verbatim; compiled here.

The $bc$–$ca$ profile kernel. Let $S, T \subseteq [n]$, and for a profile $p \colon \mathrm{Fin}\,n \to
\mathrm{Fin}\,6$ write $x(p)$ for its $bc$-vote vector and $y(p)$ for its $ca$-vote
vector, each lying in $\{0,1\}^n$. Averaging the product of Walsh characters over all
$6^n$ profiles gives
\[
  \left(\tfrac{1}{6}\right)^{n} \sum_{p} \chi_S\bigl(x(p)\bigr)\,\chi_T\bigl(y(p)\bigr)
  \;=\;
\begin{cases} \left(-\tfrac{1}{3}\right)^{\abs{S}} & \text{if } S = T,\\[2pt] 0 &
\text{if } S \ne T. \end{cases}
\]
-/

set_option maxHeartbeats 800000 in
open scoped BigOperators in
open BooleanAnalysis in
variable {n : ℕ} in
/-- Kernel lemma for the bc–ca pair. -/
lemma ArrowTheorem.profile_kernel_bcca (S T : Finset (Fin n)) :
    (1/6 : ℝ)^n * ∑ p : Profile n,
      chiS S (bcVotes p) * chiS T (caVotes p) =
    if S = T then (-1/3 : ℝ)^S.card else 0 :=
  profile_kernel_gen sum_bcPref_sign sum_caPref_sign sum_bcPref_caPref S T
