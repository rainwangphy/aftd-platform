import AFTD.Prelude
import AFTD.Kb.Tcs.VSub
import AFTD.Kb.Tcs.ExtendFromC
import AFTD.Kb.Tcs.RestrictToC

/-!
# extendFromC_restrictToC

Topic: quantum   Node: 227b36d88423

Provenance: helper lemma. TCSlib, `extendFromC_restrictToC`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean (Apache-2.0); 1 verbatim; compiled here.

Extension recovers a vector supported on $C$. Fix a prime $p$ and a subset $C \subseteq \{1,\dots,n\}$ of coordinates, and let $V_C
\subseteq \mathbb{F}_p^n \times \mathbb{F}_p^n$ be the submodule of pairs of vectors
whose support is contained in $C$. Then extending back the coordinate functions of a
supported vector recovers that vector exactly: for every $x \in V_C$, applying the
restriction map $V_C \to (C \to \mathbb{F}_p) \times (C \to \mathbb{F}_p)$ and then the
extension-by-zero map back into $V_C$ returns $x$. Equivalently, the extension map is a
left inverse of the restriction map.
-/

open scoped BigOperators in
set_option linter.mathlibStandardSet false in
open scoped BigOperators in
open scoped Real in
open scoped Nat in
open Classical in
open scoped Pointwise in
set_option maxRecDepth 4000 in
set_option synthInstance.maxHeartbeats 20000 in
set_option synthInstance.maxSize 128 in
set_option relaxedAutoImplicit false in
set_option autoImplicit false in
set_option linter.unnecessarySimpa false in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
lemma extendFromC_restrictToC (C : Finset (Fin n)) :
    ∀ x, extendFromC (p:=p) C (restrictToC (p:=p) C x) = x := by
  classical
  rintro ⟨v, hv⟩
  have hv' : ∀ j, j ∉ C → v.1 j = 0 ∧ v.2 j = 0 := by
    simpa [V_sub] using hv
  apply Subtype.ext
  ext i
  · by_cases hi : i ∈ C
    · simp [extendFromC, restrictToC, hi]
    · have h0 := (hv' i hi).1
      simp [extendFromC, restrictToC, hi, h0]
  · by_cases hi : i ∈ C
    · simp [extendFromC, restrictToC, hi]
    · have h0 := (hv' i hi).2
      simp [extendFromC, restrictToC, hi, h0]
