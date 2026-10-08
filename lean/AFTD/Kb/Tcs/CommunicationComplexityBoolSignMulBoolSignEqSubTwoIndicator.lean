import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityBoolSign

/-!
# CommunicationComplexity.boolSign_mul_boolSign_eq_sub_two_indicator

Topic: communication   Node: 6e17ccd70911

Provenance: helper lemma. TCSlib, `CommunicationComplexity.boolSign_mul_boolSign_eq_sub_two_indicator`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/Helper.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Product of two Boolean signs. For all Boolean values $a$ and $b$, the product of their signs satisfies
\[
  \mathrm{sign}(a)\cdot\mathrm{sign}(b) \;=\; 1 - 2\,\mathbf{1}[a \ne b],
\]
where $\mathrm{sign}(\cdot)$ sends $\mathrm{false}$ to $1$ and $\mathrm{true}$ to $-1$,
and $\mathbf{1}[a \ne b]$ is $1$ when $a$ and $b$ differ and $0$ when they agree.
Equivalently, this product equals $1$ when the two bits are equal and $-1$ when they
disagree.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- Two `boolSign` factors collapse to `1 - 2 * indicator(a ≠ b)`. -/
lemma CommunicationComplexity.boolSign_mul_boolSign_eq_sub_two_indicator
    (a b : Bool) :
    boolSign a * boolSign b = (1 : ℝ) - 2 * (if a ≠ b then 1 else 0) := by
  cases a <;> cases b <;> norm_num [boolSign]
