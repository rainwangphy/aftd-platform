import AFTD.Prelude

/-!
# ProbabilityTheory.HasBernsteinMGF

Topic: concentration   Node: dc927d964691

Provenance: formalization of a published result. Source: TCSlib, `ProbabilityTheory.HasBernsteinMGF`. Lean proof by Ganesh Sankar, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/JohnsonLindenstrauss/Bernstein.lean (Copyright (c) 2026 Ganesh Sankar. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

$\texttt{ProbabilityTheory.HasBernsteinMGF}\ X\ \mu\ c\ t_{\max}$ is a
predicate on a random variable $X : \Omega \to \mathbb{R}$, a measure
$\mu$, and real parameters $c, t_{\max} \ge 0$.  It asserts that for
every $t$ with $|t| \le t_{\max}$, the exponential moment
$e^{tX}$ is $\mu$-integrable, and the moment generating function
satisfies $\mathbf{E}_\mu[e^{tX}] \le e^{c t^2}$.  The pair
$(c, t_{\max})$ parametrizes a ``two-parameter sub-exponential'' family:
$c$ controls the quadratic growth near zero and $t_{\max}$ bounds the
radius of validity.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory ProbabilityTheory Real in
variable {Ω : Type*} {mΩ : MeasurableSpace Ω} in
/-- A real random variable `X` on the measure space `(Ω, μ)` has a *Bernstein-type moment generating function* with parameters `(c, tmax)` if, for every real `t` with `|t| ≤ tmax`, the function `exp(t·X)` is `μ`-integrable and its mean — the moment generating function of `X` at `t` — is at most `exp(c·t²)`. This is the sub-exponential MGF condition of [Ver18, Prop 2.7.1(e)] (`E exp(λX) ≤ exp(K²λ²)` for `|λ| ≤ 1/K`), with `c = K²` and `tmax = 1/K`. Deviation from the source: the two parameters `c` and `tmax` are explicit and independent of each other (the source ties both to a single sub-exponential norm `K`), and the integrability of `exp(t·X)` on the range is recorded as a field rather than derived. `HasBernsteinMGF X μ c tmax` says the MGF of `X` under `μ` is bounded by the Gaussian envelope `exp(c t²)` on `|t| ≤ tmax`, with `exp(t · X)` integrable on the same range. The pair `(c, tmax)` parametrizes a "two-parameter sub-exponential" family: `c` controls the local quadratic behavior near zero; `tmax` bounds the radius of the MGF's domain (which may be finite for genuinely sub-exponential — but not sub-Gaussian — RVs). For sub-Gaussian `X` (with parameter `σ²`) one can take `tmax = ∞` formally; this predicate is more useful when `tmax < ∞`. -/
structure ProbabilityTheory.HasBernsteinMGF (X : Ω → ℝ) (μ : Measure Ω) (c tmax : ℝ) : Prop where
  integrable : ∀ t : ℝ, |t| ≤ tmax → Integrable (fun ω => Real.exp (t * X ω)) μ
  mgf_le : ∀ t : ℝ, |t| ≤ tmax → mgf X μ t ≤ Real.exp (c * t ^ 2)
