import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremBcPref
import AFTD.Kb.GameTheoryEconomics.ArrowTheoremCaPref
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSign

/-!
# ArrowTheorem.sum_bcPref_caPref

Topic: social_choice   Node: aab13b3c4ab9

Provenance: helper lemma. TCSlib, `ArrowTheorem.sum_bcPref_caPref`. Lean proof by Mina, Allan Li, Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/ArrowTheorem.lean (Apache-2.0); 1 verbatim; compiled here.

Sum of paired preference signs. Label the six strict orderings of three alternatives $a,b,c$ by $k\in\{0,\dots,5\}$. For
each ordering let $x_k\in\{-1,+1\}$ record the $a$-versus-$b$ comparison, taking the
value $+1$ when $a$ is preferred to $b$ and $-1$ when $b$ is preferred to $a$, and let
$y_k\in\{-1,+1\}$ record the $b$-versus-$c$ comparison in the same way, with $+1$ when
$b$ is preferred to $c$ and $-1$ otherwise. Then
\[
\sum_{k=0}^{5} x_k\,y_k \;=\; -2.
\]

For each of the six strict orderings $k \in \{0,\dots,5\}$ of three alternatives
$a,b,c$, let $\sigma$ be the sign encoding, sending $\mathrm{false}$ to $+1$ and
$\mathrm{true}$ to $-1$. Write $y_k = \sigma(p_k)$, where $p_k$ is the Boolean
preference of ordering $k$ in the $b$-vs-$c$ comparison, and $z_k = \sigma(q_k)$, where
$q_k$ is the preference in the $c$-vs-$a$ comparison. Then
\[
\sum_{k=0}^{5} y_k\, z_k \;=\; -2.
\]

For each of the six strict orderings $k \in \{0,\dots,5\}$ of three alternatives
$a,b,c$, write $p_{ab}(k)$ and $p_{ca}(k)$ for the Boolean preferences of ordering $k$
in the $a$-vs-$b$ and $c$-vs-$a$ comparisons, and let $\sigma$ be the sign encoding
sending $\mathrm{false}$ to $1$ and $\mathrm{true}$ to $-1$. Then the sum over all six
orderings of the products of the encoded signs is
\[
\sum_{k=0}^{5} \sigma\big(p_{ab}(k)\big)\,\sigma\big(p_{ca}(k)\big)
\;=\; -2.
\]
-/

set_option maxHeartbeats 800000 in
open scoped BigOperators in
open BooleanAnalysis in
variable {n : ℕ} in
/-- Similarly, E[s_bc · s_ca] = -1/3. -/
lemma ArrowTheorem.sum_bcPref_caPref :
    ∑ k : Fin 6, boolToSign (bcPref k) * boolToSign (caPref k) = -2 := by
  simp only [Fin.sum_univ_six, bcPref, caPref, boolToSign]
  norm_num
