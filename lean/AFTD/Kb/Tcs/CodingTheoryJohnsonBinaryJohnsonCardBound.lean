import AFTD.Prelude
import AFTD.Kb.Tcs.CodingTheoryJohnsonBitVec
import AFTD.Kb.Tcs.CodingTheoryJohnsonJ2
import AFTD.Kb.Tcs.CodingTheoryJohnsonAlpha
import AFTD.Kb.Tcs.CodingTheoryJohnsonAlphaLtOneOfHd1
import AFTD.Kb.Tcs.CodingTheoryJohnsonAlphaNonneg
import AFTD.Kb.Tcs.CodingTheoryJohnsonBinaryJohnsonCardBoundParametric
import AFTD.Kb.Tcs.CodingTheoryJohnsonHdist
import AFTD.Kb.Tcs.CodingTheoryJohnsonJohnsonArith
import AFTD.Kb.Tcs.CodingTheoryJohnsonShifted
import AFTD.Kb.Tcs.CodingTheoryJohnsonShiftedNeZeroOfAlphaLtOne
import AFTD.Kb.Tcs.CodingTheoryJohnsonWt
import AFTD.Kb.Tcs.CodingTheoryJohnsonPmOneApplyFalse
import AFTD.Kb.Tcs.CodingTheoryJohnsonPmOneApplyTrue
import AFTD.Kb.Tcs.Wt

/-!
# CodingTheory.Johnson.binary_johnson_card_bound

Topic: information   Node: 804c24fedd96

Provenance: formalization of a published result. Source: Binary Johnson cardinality bound, as formalized in TCSlib (`CodingTheory.Johnson.binary_johnson_card_bound`). Lean proof by Allan Li, Frederick Dehmel, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/JohnsonBound.lean (Apache-2.0); 1 verbatim; compiled here.

Binary Johnson cardinality bound. Let $n \ge 1$ and let $d$ be an integer with $1 \le d$ and $2d \le n$. Suppose $C$ is a
finite set of binary words of length $n$ such that any two distinct words of $C$ are at
Hamming distance at least $d$, and every word of $C$ has Hamming weight at most $w$. If
$w \le J_2(n,d)$, where $J_2(n,d) = \tfrac{1}{2}\bigl(n - \sqrt{n(n-2d)}\bigr)$ is the
binary Johnson radius, then $\abs{C} \le 2n$.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators RealInnerProductSpace in
open Finset in
open Classical in
open scoped RealInnerProductSpace in
open scoped InnerProductSpace in
open Finset in
theorem CodingTheory.Johnson.binary_johnson_card_bound
    {n d w : ℕ}
    (hn : 0 < n)
    (hd1 : 1 ≤ d)
    (hd : 2 * d ≤ n)
    (C : Finset (BitVec n))
    (hpair : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → d ≤ hdist x y)
    (hwt : ∀ x ∈ C, wt x ≤ w)
    (hwJ : (w : ℝ) ≤ J2 n d) :
    C.card ≤ 2 * n := by
  let α : ℝ := alpha n d

  have hα0 : 0 ≤ α := by
    simpa [α] using alpha_nonneg n d

  have hα1 : α < 1 := by
    simpa [α] using alpha_lt_one_of_hd1 (n := n) (d := d) hn hd1 hd

  have hnonzero : ∀ x ∈ C, shifted α x ≠ 0 := by
    intro x hx
    exact shifted_ne_zero_of_alpha_lt_one (n := n) hn hα0 hα1 x

  have harith :
      ((n : ℝ) - 2 * (d : ℝ))
        + α^2 * (n : ℝ)
        + 2 * α * (2 * (w : ℝ) - (n : ℝ))
        ≤ 0 := by
    simpa [α] using johnson_arith (n := n) (d := d) (w := w) hn hd hwJ

  exact binary_johnson_card_bound_parametric
    (n := n) (d := d) (w := w)
    hn C hpair hwt α hα0 hnonzero harith
