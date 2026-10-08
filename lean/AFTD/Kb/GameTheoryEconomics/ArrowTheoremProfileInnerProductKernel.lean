import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremProfile
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremAbVotes
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremBcVotes
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremSumAbPrefBcPref
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremProfileKernelGen
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremSumAbPrefSign
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremSumBcPrefSign
import AFTD.Kb.Tcs.BooleanAnalysisChiS

/-!
# ArrowTheorem.profile_inner_product_kernel

Topic: social_choice   Node: ff357c98809a

Provenance: helper lemma. TCSlib, `ArrowTheorem.profile_inner_product_kernel`. Lean proof by Mina, Allan Li, Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/ArrowTheorem.lean (Apache-2.0); 1 verbatim; compiled here.

Orthogonality kernel for the $ab$–$bc$ vote pair. Fix $n$, and for each profile $p \in \{0,\dots,5\}^n$ let $v_{ab}(p), v_{bc}(p) \in
\{0,1\}^n$ be the vote vectors recording, voter by voter, each voter's pairwise
preference in the $a$-vs-$b$ and $b$-vs-$c$ comparisons, and for $S \subseteq [n]$ let
$\chi_S$ be the associated Walsh–Fourier character. Then for all subsets $S, T \subseteq
[n]$, the uniform average of the product $\chi_S(v_{ab}(p))\,\chi_T(v_{bc}(p))$ over the
$6^n$ profiles satisfies
\[
  \Bigl(\tfrac{1}{6}\Bigr)^{\!n}\sum_{p}
    \chi_S\bigl(v_{ab}(p)\bigr)\,\chi_T\bigl(v_{bc}(p)\bigr)
  \;=\;
\begin{cases} \left(-\tfrac{1}{3}\right)^{\abs{S}} & S = T,\\[2pt] 0 & S \ne T.
\end{cases}
\]
-/

set_option maxHeartbeats 800000 in
open scoped BigOperators in
open BooleanAnalysis in
variable {n : ℕ} in
/-- Kernel lemma for the ab–bc pair. -/
lemma ArrowTheorem.profile_inner_product_kernel (S T : Finset (Fin n)) :
    (1/6 : ℝ)^n * ∑ p : Profile n,
      chiS S (abVotes p) * chiS T (bcVotes p) =
    if S = T then (-1/3 : ℝ)^S.card else 0 :=
  profile_kernel_gen sum_abPref_sign sum_bcPref_sign sum_abPref_bcPref S T
