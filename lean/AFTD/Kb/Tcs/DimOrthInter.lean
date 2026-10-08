import AFTD.Prelude
import AFTD.Kb.Tcs.SymOrth
import AFTD.Kb.Tcs.SymFormSubIsRefl
import AFTD.Kb.Tcs.OrthInterEqOrthSubImage
import AFTD.Kb.Tcs.SymBApply
import AFTD.Kb.Tcs.SymFormSub
import AFTD.Kb.Tcs.DimVSub
import AFTD.Kb.Tcs.VSub
import AFTD.Kb.Tcs.RE
import AFTD.Kb.Tcs.SymFormSubApply
import AFTD.Kb.Tcs.V
import AFTD.Kb.Tcs.F
import AFTD.Kb.Tcs.SymFormSubNondegenerate

/-!
# dim_orth_inter

Topic: quantum   Node: d00447014b07

Provenance: helper lemma. TCSlib, `dim_orth_inter`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean (Apache-2.0); 1 adapted; compiled here.

Dimension of the orthogonal intersection over a coordinate set. Fix a prime $p$, an integer $n$, and work in the symplectic space $V = \bbf_p^{\,n}
\times \bbf_p^{\,n}$ equipped with the symplectic form $\omega\big((x,z),(x',z')\big) =
\sum_{i} (x_i z'_i - z_i x'_i)$. Let $M$ be a subset of the coordinate set
$\{0,1,\dots,n-1\}$, let $V_M \le V$ be the support submodule of vectors whose
coordinates vanish outside $M$, and let $r_M : V \to V_M$ be the restriction map that
zeroes every coordinate outside $M$. Then for any $\bbf_p$-subspace $S \le V$, the
symplectic orthogonal complement $S^{\perp_\omega}$ satisfies
\[
\dim_{\bbf_p}\big(S^{\perp_\omega} \cap V_M\big) \;=\; 2\,\abs{M} \;-\;
\dim_{\bbf_p}\big(r_M(S)\big).
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
/-- Dimension of orthogonal intersection -/
lemma dim_orth_inter (M : Finset (Fin n)) (S : Submodule (F p) (V n p)) :
    Module.finrank (F p) ↥(sym_orth S ⊓ V_sub (p:=p) M) = 2 * M.card - Module.finrank (F p) ↥(S.map (r_E M)) := by
      have h_image : sym_orth S ⊓ V_sub M = ((sym_form_sub M).orthogonal (S.map (r_E M))).map (V_sub M).subtype := by
        convert orth_inter_eq_orth_sub_image M S using 1;
      have h_orthogonal_complement : ∀ (W : Submodule (F p) (V_sub (p:=p) M)), Module.finrank (F p) ((sym_form_sub M).orthogonal W) = Module.finrank (F p) (V_sub (p:=p) M) - Module.finrank (F p) W := by
        have h_orthogonal_complement : ∀ (W : Submodule (F p) (V_sub (p:=p) M)), (sym_form_sub (p:=p) M).IsRefl → (sym_form_sub (p:=p) M).Nondegenerate → Module.finrank (F p) ((sym_form_sub (p:=p) M).orthogonal W) = Module.finrank (F p) (V_sub (p:=p) M) - Module.finrank (F p) W := by
          exact fun W a a_1 => LinearMap.BilinForm.finrank_orthogonal a_1 W;
        exact fun W => h_orthogonal_complement W ( sym_form_sub_isRefl M ) ( sym_form_sub_nondegenerate M );
      convert h_orthogonal_complement ( S.map ( r_E M ) ) using 1;
      · rw [ h_image, ← Submodule.finrank_map_subtype_eq ];
      · rw [ dim_V_sub ]

/-
Expansion of g(M) in terms of dimensions of S and intersections.
-/
