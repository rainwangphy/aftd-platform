import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremAcyclic
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremAcyclicImpliesCorrFunc
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremCorrFunc
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremCorrFuncEqNegThirdOfWeightOne
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremDegreeOneImpliesDictator
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremIsDictator
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremUnanimity
import AFTD.Kb.Tcs.BooleanAnalysisBooleanFunc
import AFTD.Kb.Tcs.BooleanAnalysisFourierCoeff
import AFTD.Kb.Tcs.BooleanAnalysisIsOddFunc
import AFTD.Kb.Tcs.BooleanAnalysisIsPmOne

/-!
# ArrowTheorem.arrow_theorem

Topic: social_choice   Node: 836b9ba99809

Provenance: formalization of a published result. Source: Arrow's impossibility theorem, as formalized in TCSlib (`ArrowTheorem.arrow_theorem`). Lean proof by Mina, Allan Li, Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/ArrowTheorem.lean (Apache-2.0); 1 verbatim; compiled here.

Arrow's impossibility theorem. Let $n$ be a natural number and let $f:\{0,1\}^n\to\bbr$ be a social welfare function
that aggregates the pairwise opinions of $n$ voters. Suppose $f$ is odd, meaning $f(\bar
x) = -f(x)$ for every $x$, where $\bar x$ is the bitwise complement of $x$; is $\pm
1$-valued, meaning $f(x)\in\{-1,1\}$ for every $x$; is unanimous, meaning $f$ takes the
value $1$ at the all-zeros input; and is acyclic, meaning that no profile of voter
orderings produces a Condorcet cycle. Here a profile assigns to each of the $n$ voters
one of the six linear orderings of three alternatives $a,b,c$, and from it one forms
three vote vectors in $\{0,1\}^n$ whose $i$-th entries record voter $i$'s preference in
the $a$-vs-$b$, $b$-vs-$c$, and $c$-vs-$a$ comparisons; acyclicity requires that $f$
never sends all three of these vectors to $1$, and never sends all three to $-1$. Then
$f$ is a dictatorship: there is a voter $i$ such that $f(x) = (-1)^{x_i}$ for all $x$.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
set_option maxHeartbeats 800000 in
open scoped BigOperators in
open BooleanAnalysis in
variable {n : ℕ} in
/-- **Arrow's Impossibility Theorem** (via Kalai's Fourier proof): Any social welfare function f that is: - odd (antisymmetric: f(¬x) = -f(x)) - ±1-valued (gives definite preferences) - unanimous (unanimously preferred alternatives are socially preferred) - acyclic (no Condorcet cycles arise) must be a **dictatorship** (there is one voter whose preference always wins). The proof uses Fourier analysis on Boolean functions: 1. Acyclicity forces the Fourier cycle probability to be 0. 2. This forces all Fourier weight onto level 1 (degree-1 functions). 3. A degree-1 ±1-valued unanimous function must be a dictator. **Source:** [OD14, Ch. 2]. -/
theorem ArrowTheorem.arrow_theorem (f : BooleanFunc n) (hodd : isOddFunc f) (hpm : isPmOne f)
    (huniv : unanimity f) (hacyc : acyclic f) :
    isDictator f := by
  -- Step 1: Acyclicity implies the correlation function equals -1/3
  have hcorr : corrFunc f = -1/3 := acyclic_implies_corrFunc f hodd hpm hacyc
  -- Step 2: corrFunc = -1/3 implies all weight on level 1
  have hdeg1 : ∀ S : Finset (Fin n), S.card ≠ 1 → fourierCoeff f S = 0 :=
    corrFunc_eq_neg_third_of_weight_one hodd hpm hcorr
  -- Step 3: Degree-1 + unanimous + ±1-valued implies dictator
  exact degree_one_implies_dictator f hodd hpm huniv hdeg1
