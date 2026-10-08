import AFTD.Prelude
import AFTD.Kb.Tcs.ExtendFromC
import AFTD.Kb.Tcs.RestrictToC

/-!
# restrictToC_extendFromC

Topic: quantum   Node: 0ac7bec2573c

Provenance: helper lemma. TCSlib, `restrictToC_extendFromC`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean (Apache-2.0); 1 verbatim; compiled here.

Restriction inverts extension on coordinates in $C$. Fix a prime $p$, a natural number $n$, and a subset $C \subseteq \{0,1,\dots,n-1\}$ of
coordinates, and let $V_C$ denote the support submodule of $V = \bbf_p^n \times
\bbf_p^n$ consisting of vectors whose support lies in $C$. Let $E \colon (C \to \bbf_p)
\times (C \to \bbf_p) \to V_C$ be the extension map, which sends a pair $(f,g)$ to the
vector agreeing with $f$ and $g$ on $C$ and equal to zero off $C$, and let $R \colon V_C
\to (C \to \bbf_p) \times (C \to \bbf_p)$ be the restriction map, which sends a vector
supported on $C$ to its two component functions restricted to $C$. Then $R \circ E$ is
the identity: for every pair $x = (f,g)$ of functions $f, g \colon C \to \bbf_p$ one has
$R(E(x)) = x$.
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
lemma restrictToC_extendFromC (C : Finset (Fin n)) :
    ∀ x, restrictToC (p:=p) C (extendFromC (p:=p) C x) = x := by
  classical
  rintro ⟨f, g⟩
  apply Prod.ext
  · funext c; simp [restrictToC, extendFromC]
  · funext c; simp [restrictToC, extendFromC]
