import AFTD.Prelude
import AFTD.Kb.Tcs.F
import AFTD.Kb.Tcs.IsIsotropic
import AFTD.Kb.Tcs.V
import AFTD.Kb.Tcs.FinrankV
import AFTD.Kb.Tcs.FinrankSymOrth
import AFTD.Kb.Tcs.SymOrth
import AFTD.Kb.Tcs.SymBApply

/-!
# finrank_le_n_of_isotropic

Topic: quantum   Node: 584e19b9d74d

Provenance: helper lemma. TCSlib, `finrank_le_n_of_isotropic`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean (Apache-2.0); 1 verbatim; compiled here.

Dimension bound for isotropic subspaces. Let $p$ be a prime and equip the $2n$-dimensional space $V = \bbf_p^n \times \bbf_p^n$
over $\bbf_p$ with the symplectic form $\omega\big((x,z),(x',z')\big) = \sum_{i=1}^{n}
(x_i z'_i - z_i x'_i)$. If $S \le V$ is an isotropic subspace, meaning $\omega(u,v) = 0$
for all $u, v \in S$, then $\dim_{\bbf_p} S \le n$.
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
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
variable {n : ℕ} {p : ℕ} [Fact p.Prime] in
lemma finrank_le_n_of_isotropic (S : Submodule (F p) (V n p)) (hS : IsIsotropic (n:=n) (p:=p) S) :
    Module.finrank (F p) S ≤ n := by
  classical
  have hmono :
      Module.finrank (F p) S ≤ Module.finrank (F p) (sym_orth (n:=n) (p:=p) S) :=
    Submodule.finrank_mono hS
  have hineq :
      Module.finrank (F p) S ≤ 2 * n - Module.finrank (F p) S := by
    simpa [finrank_sym_orth (n:=n) (p:=p) S] using hmono
  have a_le_2n :
      Module.finrank (F p) S ≤ 2 * n := by
    have : Module.finrank (F p) S ≤ Module.finrank (F p) (V n p) := by
      simpa using (Submodule.finrank_le (R := F p) (M := V n p) S)
    simpa [finrank_V (n:=n) (p:=p)] using this
  have h2 : 2 * Module.finrank (F p) S ≤ 2 * n := by
    have hadd :
        Module.finrank (F p) S + Module.finrank (F p) S ≤ 2 * n := by
      exact (Nat.le_sub_iff_add_le a_le_2n).1 hineq
    simpa [two_mul] using hadd
  exact Nat.le_of_mul_le_mul_left h2 (by decide : 0 < 2)
