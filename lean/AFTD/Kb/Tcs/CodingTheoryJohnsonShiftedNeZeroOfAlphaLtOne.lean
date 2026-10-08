import AFTD.Prelude
import AFTD.Kb.Tcs.CodingTheoryJohnsonBitVec
import AFTD.Kb.Tcs.CodingTheoryJohnsonEuc
import AFTD.Kb.Tcs.CodingTheoryJohnsonOnes
import AFTD.Kb.Tcs.CodingTheoryJohnsonPmOne
import AFTD.Kb.Tcs.CodingTheoryJohnsonShifted

/-!
# CodingTheory.Johnson.shifted_ne_zero_of_alpha_lt_one

Topic: information   Node: 5730a5c98d02

Provenance: helper lemma. TCSlib, `CodingTheory.Johnson.shifted_ne_zero_of_alpha_lt_one`. Lean proof by Allan Li, Frederick Dehmel, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/JohnsonBound.lean (Apache-2.0); 1 verbatim; compiled here.

Shifted $\pm 1$ vectors are nonzero for $\alpha < 1$. Let $n \ge 1$ and let $\alpha$ be a real number with $0 \le \alpha < 1$. Then for every
binary word $x$ of length $n$, the shifted vector $\hat{x}^\alpha \in \bbr^n$ — obtained
from the $\pm 1$ embedding of $x$ by subtracting $\alpha$ times the all-ones vector — is
nonzero.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators RealInnerProductSpace in
open Finset in
open Classical in
open scoped RealInnerProductSpace in
open scoped InnerProductSpace in
open Finset in
lemma CodingTheory.Johnson.shifted_ne_zero_of_alpha_lt_one
    {n : ℕ} (hn : 0 < n) {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α < 1) (x : BitVec n) :
    shifted α x ≠ 0 := by
  intro hzero
  let i : Fin n := ⟨0, hn⟩
  have hcoord : shifted α x i = 0 := by
    have h := congrArg (fun v : Euc n => v i) hzero
    simpa using h
  by_cases hx : x i
  · have hform : shifted α x i = (-1 : ℝ) - α := by
      simp [shifted, pmOne, ones, hx]
    linarith
  · have hform : shifted α x i = (1 : ℝ) - α := by
      simp [shifted, pmOne, ones, hx]
    linarith
