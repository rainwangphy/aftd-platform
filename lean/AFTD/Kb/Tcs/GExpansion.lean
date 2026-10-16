import AFTD.Prelude
import AFTD.Kb.Tcs.EC
import AFTD.Kb.Tcs.F
import AFTD.Kb.Tcs.IsIsotropic
import AFTD.Kb.Tcs.SM
import AFTD.Kb.Tcs.SPerpM
import AFTD.Kb.Tcs.V
import AFTD.Kb.Tcs.VSub
import AFTD.Kb.Tcs.DimVSub
import AFTD.Kb.Tcs.DimMapRE
import AFTD.Kb.Tcs.DimOrthInter
import AFTD.Kb.Tcs.G
import AFTD.Kb.Tcs.RE
import AFTD.Kb.Tcs.SymOrth
import AFTD.Kb.Tcs.SymBApply
import AFTD.Kb.Tcs.SymFormSubApply

/-!
# g_expansion

Topic: quantum   Node: 91d449359c2b

Provenance: helper lemma. TCSlib, `g_expansion`. Lean proof by Allan Li, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/QuantumSingleton.lean (Apache-2.0); 1 adapted; compiled here.

Expansion of the operator count $g(S,M)$. Fix a prime $p$ and equip $V = \bbf_p^{\,n} \times \bbf_p^{\,n}$ with the symplectic
form $\omega\big((x,z),(x',z')\big) = \sum_{i=0}^{n-1}\big(x_i z'_i - z_i x'_i\big)$.
For a set of coordinates $M \subseteq \{0,\dots,n-1\}$, let $V_M \le V$ be the subspace
of vectors supported on $M$, and for a subspace $W \le V$ write $W_M = W \cap V_M$. Let
$S \le V$ be isotropic, meaning $\omega(u,v) = 0$ for all $u,v \in S$, let $S^{\perp}$
denote its symplectic orthogonal complement, and set $g(S,M) =
\dim_{\bbf_p}\!\big(S^{\perp}\cap V_M\big) - \dim_{\bbf_p}(S_M)$. Then, writing $M^c$
for the complementary set of coordinates,
\[
g(S,M) \;=\; 2\,\abs{M} + \dim_{\bbf_p}\!\big(S_{M^c}\big) - \dim_{\bbf_p}(S) -
\dim_{\bbf_p}(S_M).
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
lemma g_expansion (S : Submodule (F p) (V n p)) (hS : IsIsotropic S) (M : Finset (Fin n)) :
    g S M = 2 * M.card + Module.finrank (F p) (S_M S (E_c M)) - Module.finrank (F p) S - Module.finrank (F p) (S_M S M) := by
      have h_g : g S M = 2 * M.card - Module.finrank (F p) (S.map (r_E M)) - Module.finrank (F p) (S_M S M) := by
        unfold g;
        rw [ show S_perp_M S M = sym_orth S ⊓ V_sub ( p := p ) M from rfl, dim_orth_inter ];
      -- By definition of $r_E$, we know that
      have h_dim_map : Module.finrank (F p) (S.map (r_E M)) = Module.finrank (F p) S - Module.finrank (F p) (S_M S (E_c M)) := by
        convert dim_map_r_E S M using 1;
        rfl
      rw [ h_g, h_dim_map, tsub_tsub ];
      rw [ tsub_tsub, add_comm ];
      rw [ tsub_eq_of_eq_add ];
      rw [ tsub_add_eq_add_tsub ];
      · rw [ Nat.sub_eq_of_eq_add ];
        rw [ ← add_assoc, add_comm ];
        rw [ tsub_add_eq_add_tsub ];
        · exact Nat.sub_eq_of_eq_add <| by ring;
        · exact Submodule.finrank_mono <| inf_le_left;
      · have h_dim_S_map : Module.finrank (F p) (S.map (r_E M)) ≤ 2 * M.card := by
          have h_dim_S_map : Module.finrank (F p) (S.map (r_E M)) ≤ Module.finrank (F p) (V_sub (p:=p) M) := by
            apply_rules [ Submodule.finrank_le ];
          exact h_dim_S_map.trans ( by rw [ dim_V_sub ] );
        have h_dim_S_M : Module.finrank (F p) (S_M S M) ≤ 2 * M.card - Module.finrank (F p) (S.map (r_E M)) := by
          have h_dim_S_M : Module.finrank (F p) (S_perp_M S M) = 2 * M.card - Module.finrank (F p) (S.map (r_E M)) := by
            convert dim_orth_inter M S using 1;
            rfl
          refine' h_dim_S_M ▸ Submodule.finrank_mono _;
          exact fun x hx => ⟨ hS hx.1, hx.2 ⟩;
        omega

/-
The complement of the complement is the original set.
-/
