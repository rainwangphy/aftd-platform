import AFTD.Prelude

/-!
# CommunicationComplexity.exp_sub_cgf_eq

Topic: information   Node: 5c29914751a8

Provenance: helper lemma. TCSlib, `CommunicationComplexity.exp_sub_cgf_eq`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/Pinsker.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Factorisation of the CGF-tilted exponential. Let $\mu$ be a measure on a measurable space $\Omega$, let $X\colon \Omega \to \bbr$,
and let $t \in \bbr$. Writing $\Lambda(t)$ for the cumulant generating function of $X$
under $\mu$ at $t$, the functions $x \mapsto e^{\,t X(x) - \Lambda(t)}$ and
$x \mapsto e^{-\Lambda(t)} \cdot e^{\,t X(x)}$ are equal, i.e.\ the tilted exponential
factors as the constant $e^{-\Lambda(t)}$ times $e^{\,tX}$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open ProbabilityTheory in
open scoped ENNReal in
/-- Function-level rewrite shared by `integral_exp_sub_cgf_eq_one` and `integrable_exp_sub_cgf`: `exp (t X - cgf X μ t)` is the constant `exp (-cgf X μ t)` times `exp (t X)`. -/
theorem CommunicationComplexity.exp_sub_cgf_eq
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (X : Ω → ℝ) (t : ℝ) :
    (fun x => Real.exp (t * X x - ProbabilityTheory.cgf X μ t)) =
      fun x => (Real.exp (-ProbabilityTheory.cgf X μ t)) * Real.exp (t * X x) := by
  ext x
  rw [sub_eq_add_neg, Real.exp_add]
  ring
