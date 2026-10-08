import AFTD.Prelude
import AFTD.Kb.Tcs.BooleanAnalysisBoolToSign

/-!
# BooleanAnalysis.boolToSign_not

Topic: combinatorics   Node: c0d08fb5693b

Provenance: helper lemma. TCSlib, `BooleanAnalysis.boolToSign_not`. Lean proof by Jingzhen Sha, Allan Li, Hydroxyi, Mina, Owen McGinty (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/Basic.lean (Apache-2.0); 1 verbatim; compiled here.

Sign encoding of false. Under the sign encoding $\sigma\colon\mathrm{Bool}\to\{-1,1\}$, the Boolean value
$\mathrm{false}$ is sent to $1$; that is, $\sigma(\mathrm{false}) = 1$.

Under the sign encoding $\sigma\colon \mathrm{Bool}\to\{-1,1\}$, which sends the truth
value false to $1$ and true to $-1$, the truth value true is mapped to $-1$; that is,
$\sigma(\text{true}) = -1$.

For every Boolean value $b$, the sign encoding satisfies $\sigma(b)^2 = 1$.

For every $b \in \mathrm{Bool}$, the sign encoding $\sigma(b) \in \{-1,1\}$ satisfies
$\sigma(b)\cdot\sigma(b) = 1$; that is, $\sigma(b)^2 = 1$.

Let $\sigma\colon\mathrm{Bool}\to\{-1,1\}$ be the sign encoding, so that
$\sigma(\mathrm{false})=1$ and $\sigma(\mathrm{true})=-1$. Then for every Boolean value
$b$, negating $b$ flips the sign of its encoding:
\[
  \sigma(\lnot b) \;=\; -\,\sigma(b).
\]
-/

set_option maxHeartbeats 400000 in
open scoped BigOperators in
variable {n : ℕ} in
/-- `boolToSign` negates under `Bool.not`. -/
@[simp]
lemma BooleanAnalysis.boolToSign_not (b : Bool) : boolToSign (!b) = -boolToSign b := by
  cases b <;> simp [boolToSign]
