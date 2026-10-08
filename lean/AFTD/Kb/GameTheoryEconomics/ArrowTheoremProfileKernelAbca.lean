import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremProfile
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremAbVotes
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremCaVotes
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremSumAbPrefCaPref
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremProfileKernelGen
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremSumAbPrefSign
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremSumCaPrefSign
import AFTD.Kb.Tcs.BooleanAnalysisChiS

/-!
# ArrowTheorem.profile_kernel_abca

Topic: social_choice   Node: 81b5e6436037

Provenance: helper lemma. TCSlib, `ArrowTheorem.profile_kernel_abca`. Lean proof by Mina, Allan Li, Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/ArrowTheorem.lean (Apache-2.0); 1 verbatim; compiled here.

Kernel of the ab–ca vote correlation. Fix a natural number $n$ and consider profiles $p$ of $n$ voters, each of whom reports
one of the six strict orderings of the three alternatives $a, b, c$; there are $6^n$
such profiles. For a profile $p$, let $x^{ab}(p) \in \{0,1\}^n$ be the vector recording
each voter's preference in the $a$-vs-$b$ comparison, and $x^{ca}(p) \in \{0,1\}^n$ the
vector recording each voter's preference in the $c$-vs-$a$ comparison. Then for any two
subsets $S, T \subseteq \{1,\dots,n\}$, the averaged product of the corresponding
Walsh–Fourier characters satisfies
\[
\left(\tfrac{1}{6}\right)^{\!n} \sum_{p}
\chi_S\bigl(x^{ab}(p)\bigr)\,\chi_T\bigl(x^{ca}(p)\bigr)
  \;=\;
\begin{cases} \left(-\tfrac{1}{3}\right)^{|S|} & \text{if } S = T,\\[2pt] 0 & \text{if }
S \neq T, \end{cases}
\]
where the sum ranges over all $6^n$ profiles.
-/

set_option maxHeartbeats 800000 in
open scoped BigOperators in
open BooleanAnalysis in
variable {n : ℕ} in
/-- Kernel lemma for the ab–ca pair. -/
lemma ArrowTheorem.profile_kernel_abca (S T : Finset (Fin n)) :
    (1/6 : ℝ)^n * ∑ p : Profile n,
      chiS S (abVotes p) * chiS T (caVotes p) =
    if S = T then (-1/3 : ℝ)^S.card else 0 :=
  profile_kernel_gen sum_abPref_sign sum_caPref_sign sum_abPref_caPref S T
