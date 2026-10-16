import AFTD.Prelude
import AFTD.Kb.Tcs.EC
import AFTD.Kb.Tcs.F
import AFTD.Kb.Tcs.IsIsotropic
import AFTD.Kb.Tcs.SM
import AFTD.Kb.Tcs.V
import AFTD.Kb.Tcs.G
import AFTD.Kb.Tcs.GExpansion
import AFTD.Kb.Tcs.SymBApply
import AFTD.Kb.Tcs.SymFormSubApply

/-!
# g_formula

Topic: quantum   Node: dab28902725e

Provenance: helper lemma. TCSlib, `g_formula`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean (Apache-2.0); 1 verbatim; compiled here.

Dimension formula for the operator count of an isotropic subspace. Let $p$ be prime, and equip the symplectic space $V = \mathbb{F}_p^n \times
\mathbb{F}_p^n$ with its standard alternating form $\omega$. If $S \le V$ is an
isotropic subspace and $M \subseteq \{0,1,\dots,n-1\}$ is any set of coordinates, then
\[
g(S,M) \;=\; \bigl(2\,\abs{M} + \dim_{\mathbb{F}_p} S_{M^c}\bigr) \;-\;
\bigl(\dim_{\mathbb{F}_p} S + \dim_{\mathbb{F}_p} S_M\bigr),
\]
where $M^c$ is the complement of $M$ and $S_{M^c} = S \cap V_{M^c}$ consists of the
vectors of $S$ supported on $M^c$.
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
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
lemma g_formula (S : Submodule (F p) (V n p)) (hS : IsIsotropic S) (M : Finset (Fin n)) :
    g S M = (2 * M.card + Module.finrank (F p) (S_M S (E_c M))) - (Module.finrank (F p) S + Module.finrank (F p) (S_M S M)) := by
      convert g_expansion S hS M using 1;
      grind

/-
Helper identity: g(M) + dim(S_M) + dim(S) = 2|M| + dim(S_Mc).
-/
