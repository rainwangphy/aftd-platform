import AFTD.Prelude
import AFTD.Kb.Tcs.EC
import AFTD.Kb.Tcs.F
import AFTD.Kb.Tcs.IsIsotropic
import AFTD.Kb.Tcs.V
import AFTD.Kb.Tcs.CleaningDimensionIdentity
import AFTD.Kb.Tcs.Correctable
import AFTD.Kb.Tcs.CorrectableImpliesGZero
import AFTD.Kb.Tcs.G
import AFTD.Kb.Tcs.SymBApply
import AFTD.Kb.Tcs.SymFormSubApply

/-!
# g_complement_correctable

Topic: quantum   Node: 43268f98be3e

Provenance: helper lemma. TCSlib, `g_complement_correctable`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean (Apache-2.0); 1 verbatim; compiled here.

Correctable erasure and the count of supportable logical operators. Let $S$ be an isotropic subspace of the symplectic space $V = \mathbb{F}_p^n \times
\mathbb{F}_p^n$ (with $p$ prime), and let $M \subseteq \{0,1,\dots,n-1\}$ be an erasure
set that is correctable for $S$. Writing $M^c$ for the complement of $M$, one has
\[
g(S, M^c) \;=\; 2n - 2\dim_{\mathbb{F}_p} S.
\]
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
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
/-- If M is correctable, g(M^c) = 2k -/
lemma g_complement_correctable
    (S : Submodule (F p) (V n p)) (hS : IsIsotropic S) (M : Finset (Fin n))
    (h : correctable S M) :
    g S (E_c M) = 2 * n - 2 * Module.finrank (F p) S := by
  have h_g_M_zero : g S M = 0 :=
    correctable_implies_g_zero (n:=n) (p:=p) S M h
  have h_sum :
      g S M + g S (E_c M) = 2 * n - 2 * Module.finrank (F p) S :=
    cleaning_dimension_identity (n:=n) (p:=p) S hS M
  simpa [h_g_M_zero] using h_sum



/-
Checking if g_complement_correctable is defined.
-/
