import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocol
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocolRun
import AFTD.Kb.Tcs.CommunicationComplexityFiniteProbabilitySpace

/-!
# CommunicationComplexity.Deterministic.Protocol.distributionalError

Topic: communication   Node: a3334667deec

Provenance: formalization of a published result. Source: TCSlib, `CommunicationComplexity.Deterministic.Protocol.distributionalError`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/Minimax.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Given a deterministic protocol $p : \mathrm{Protocol}\,X\,Y\,\alpha$, a finite
probability space $\mu$ on $X \times Y$, and a target function $f : X \to Y \to \alpha$,
the \emph{distributional error} $p.\mathrm{distributionalError}(\mu, f) \in \mathbb{R}$
is the $\mu$-probability that the output of $p$ disagrees with $f$, i.e.\
$\mu\bigl(\{(x,y) \mid p.\mathrm{run}(x,y) \ne f(x,y)\}\bigr)$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
variable {X Y α : Type*} in
/-- The distributional error of a deterministic protocol with respect to a distribution `μ` on `X × Y`: the probability, for an input `(x, y)` drawn from `μ`, that the protocol's output disagrees with `f x y`. [RY20, Ch. 3, §Variants of Randomized Protocols: average-case error e w.r.t. µ]. -/
noncomputable def CommunicationComplexity.Deterministic.Protocol.distributionalError
    (p : Protocol X Y α)
    (μ : FiniteProbabilitySpace (X × Y))
    (f : X → Y → α) : ℝ := by
  letI := μ
  exact volume.real {xy : X × Y | p.run xy.1 xy.2 ≠ f xy.1 xy.2}
