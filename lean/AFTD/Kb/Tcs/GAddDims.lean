import AFTD.Prelude
import AFTD.Kb.Tcs.EC
import AFTD.Kb.Tcs.F
import AFTD.Kb.Tcs.IsIsotropic
import AFTD.Kb.Tcs.SM
import AFTD.Kb.Tcs.V
import AFTD.Kb.Tcs.VSub
import AFTD.Kb.Tcs.DimSMAddDimSMCLeDimS
import AFTD.Kb.Tcs.DimVSub
import AFTD.Kb.Tcs.DimMapRE
import AFTD.Kb.Tcs.DimOrthInter
import AFTD.Kb.Tcs.G
import AFTD.Kb.Tcs.GFormula
import AFTD.Kb.Tcs.RE
import AFTD.Kb.Tcs.SymOrth
import AFTD.Kb.Tcs.SymBApply
import AFTD.Kb.Tcs.SymFormSubApply
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# g_add_dims

Topic: quantum   Node: b4a989936059

Provenance: helper lemma. TCSlib, `g_add_dims`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean (Apache-2.0); 1 verbatim; compiled here.

Additive dimension identity for an isotropic subspace. Let $S$ be an isotropic submodule of the symplectic space $V=\bbf_p^n\times\bbf_p^n$,
and let $M\subseteq\{0,\dots,n-1\}$ be a set of coordinates with complement $M^c$.
Writing $S_M=S\cap V_M$ and $S_{M^c}=S\cap V_{M^c}$ for the parts of $S$ supported on
$M$ and on its complement, one has
\[
g(S,M)+\dim_{\bbf_p}(S_M)+\dim_{\bbf_p}(S) \;=\; 2\lvert M\rvert +
\dim_{\bbf_p}(S_{M^c}).
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
lemma g_add_dims (S : Submodule (F p) (V n p)) (hS : IsIsotropic S) (M : Finset (Fin n)) :
    g S M + Module.finrank (F p) (S_M S M) + Module.finrank (F p) S = 2 * M.card + Module.finrank (F p) (S_M S (E_c M)) := by
      -- By definition of $g(S, E)$, we know that
      have h_g_def := g_formula (n:=n) (p:=p) S hS M
      have := dim_S_M_add_dim_S_M_c_le_dim_S S M;
      contrapose! h_g_def;
      rw [ Ne.eq_def, eq_tsub_iff_add_eq_of_le ];
      · cases lt_or_gt_of_ne h_g_def <;> linarith;
      · have := dim_orth_inter M S;
        have := dim_map_r_E S M;
        unfold S_M at *;
        rw [ eq_tsub_iff_add_eq_of_le ] at *;
        · linarith [ show Module.finrank ( F p ) ↥ ( S ⊓ V_sub M ) ≤ Module.finrank ( F p ) ↥ ( sym_orth S ⊓ V_sub M ) from Submodule.finrank_mono <| by
                      exact inf_le_inf_right (V_sub M) hS ];
        · have := Submodule.finrank_le ( Submodule.map ( r_E M ) S );
          exact le_trans this ( by rw [ dim_V_sub ] );
        · (expose_names; exact Nat.le_of_add_left_le this_1)

/-
Inequality relating dimensions of S, S_M, and S_Mc.
-/
