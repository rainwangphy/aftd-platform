import AFTD.Prelude
import AFTD.Kb.Tcs.EC
import AFTD.Kb.Tcs.ECEC
import AFTD.Kb.Tcs.F
import AFTD.Kb.Tcs.IsIsotropic
import AFTD.Kb.Tcs.SM
import AFTD.Kb.Tcs.V
import AFTD.Kb.Tcs.G
import AFTD.Kb.Tcs.GAddDims
import AFTD.Kb.Tcs.SymBApply
import AFTD.Kb.Tcs.SymFormSubApply
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# cleaning_dimension_identity

Topic: quantum   Node: 1157a091813b

Provenance: helper lemma. TCSlib, `cleaning_dimension_identity`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean (Apache-2.0); 1 verbatim; compiled here.

Cleaning dimension identity for isotropic subspaces. Let $p$ be prime and let $S \le V = \bbf_p^n \times \bbf_p^n$ be a subspace that is
isotropic for the symplectic form $\omega$, meaning $\omega(u,v)=0$ for all $u,v \in S$.
Then for every subset $M \subseteq \{0,\dots,n-1\}$, with complement $M^c$,
\[
g(S,M) + g(S,M^c) = 2n - 2\dim_{\bbf_p} S,
\]
where $g(S,M) = \dim_{\bbf_p}\!\big(S^{\perp}_M\big) - \dim_{\bbf_p}\!\big(S_M\big)$.
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
/-- Cleaning dimension identity -/
lemma cleaning_dimension_identity (S : Submodule (F p) (V n p)) (hS : IsIsotropic S) (M : Finset (Fin n)) :
    g S M + g S (E_c M) = 2 * n - 2 * Module.finrank (F p) S := by
      have h1 : g S M + Module.finrank (F p) (S_M S M) + Module.finrank (F p) S = 2 * M.card + Module.finrank (F p) (S_M S (E_c M)) := by
          exact g_add_dims (n:=n) (p:=p) S hS M
      have h2 : g S (E_c M) + Module.finrank (F p) (S_M S (E_c M)) + Module.finrank (F p) S = 2 * (E_c M).card + Module.finrank (F p) (S_M S M) := by
        convert g_add_dims S hS ( E_c M ) using 1;
        rw [ E_c_E_c ];
      unfold E_c at *; simp_all +decide [ Finset.card_compl ] ;
      exact eq_tsub_of_add_eq ( by linarith [ Nat.sub_add_cancel ( show M.card ≤ n from le_trans ( Finset.card_le_univ _ ) ( by norm_num ) ) ] )

/-
Cardinality of M plus cardinality of M^c is n.
-/
