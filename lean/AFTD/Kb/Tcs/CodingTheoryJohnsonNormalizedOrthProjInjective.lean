import AFTD.Prelude
import AFTD.Kb.Tcs.CodingTheoryJohnsonOrthProj
import AFTD.Kb.Tcs.CodingTheoryJohnsonOrthProjNeZero

/-!
# CodingTheory.Johnson.normalized_orthProj_injective

Topic: information   Node: c106919e151c

Provenance: helper lemma. TCSlib, `CodingTheory.Johnson.normalized_orthProj_injective`. Lean proof by Allan Li, Frederick Dehmel, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/JohnsonBound.lean (Apache-2.0); 1 adapted; compiled here.

Distinct normalized projections off a unit vector. Let $u,v,w$ be unit vectors in a real inner product space satisfying $\langle v,u\rangle
\le 0$, $\langle w,u\rangle \le 0$, and $\langle v,w\rangle \le 0$, and suppose that
neither $v$ nor $w$ equals $u$ or $-u$ and that $v \neq w$. For $x$ in the space write
$\pi(x) = x - \langle u,x\rangle\,u$ for the projection of $x$ onto the orthogonal
complement of $\mathrm{span}\{u\}$. Then the two normalized projections
$\norm{\pi(v)}^{-1}\,\pi(v)$ and $\norm{\pi(w)}^{-1}\,\pi(w)$ cannot be equal.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators RealInnerProductSpace in
open Finset in
open Classical in
open scoped RealInnerProductSpace in
open scoped InnerProductSpace in
open Finset in
open Classical in
attribute [local instance] Classical.dec in
lemma CodingTheory.Johnson.normalized_orthProj_injective {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    (u v w : V) (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) (hw : ‖w‖ = 1)
    (hvu : inner ℝ v u ≤ 0) (hwu : inner ℝ w u ≤ 0)
    (hvw_ip : inner ℝ v w ≤ 0)
    (hv1 : v ≠ u) (hv2 : v ≠ -u) (hw1 : w ≠ u) (hw2 : w ≠ -u)
    (_hvw : v ≠ w)
    (h_eq : (‖orthProj u v‖⁻¹ • orthProj u v : V) =
            (‖orthProj u w‖⁻¹ • orthProj u w : V)) :
    False := by
      -- From h_eq, we have orthProj u v = c • orthProj u w with c = ‖orthProj u v‖/‖orthProj u w‖ > 0.
      obtain ⟨c, hc⟩ : ∃ c : ℝ, 0 < c ∧ orthProj u v = c • orthProj u w := by
        refine' ⟨ ‖orthProj u v‖ / ‖orthProj u w‖, div_pos ( norm_pos_iff.mpr ( orthProj_ne_zero u v hu hv hv1 hv2 ) ) ( norm_pos_iff.mpr ( orthProj_ne_zero u w hu hw hw1 hw2 ) ), _ ⟩;
        convert congr_arg ( fun x => ‖orthProj u v‖ • x ) h_eq using 1 <;> norm_num [ div_eq_mul_inv, smul_smul ];
        rw [ mul_inv_cancel₀ ] <;> norm_num;
        exact orthProj_ne_zero u v hu hv hv1 hv2;
      -- Compute ⟪v,w⟫ = c(1 - ⟪u,w⟫²) + ⟪u,v⟫⟪u,w⟫.
      have h_inner : ⟪v, w⟫_ℝ = c * (1 - ⟪u, w⟫_ℝ ^ 2) + ⟪u, v⟫_ℝ * ⟪u, w⟫_ℝ := by
        have h_sub : v - ⟪u, v⟫_ℝ • u = c • (w - ⟪u, w⟫_ℝ • u) := hc.2
        -- Substitute h_sub into the inner product expression.
        have h_inner : ⟪v, w⟫_ℝ = ⟪c • (w - ⟪u, w⟫_ℝ • u) + ⟪u, v⟫_ℝ • u, w⟫_ℝ := by
          rw [ ← h_sub, sub_add_cancel ];
        rw [ h_inner, inner_add_left, inner_smul_left, inner_sub_left, inner_smul_left ] ; ring_nf;
        simp +decide [ mul_comm, mul_left_comm, inner_smul_left ] ; rw [hw]; ring
      -- Since $w \neq \pm u$, we have $|⟪u, w⟫| < 1$.
      have h_abs : |⟪u, w⟫_ℝ| < 1 := by
        have h_abs : ‖w - u‖ > 0 ∧ ‖w + u‖ > 0 := by
          exact ⟨ norm_pos_iff.mpr ( sub_ne_zero.mpr hw1 ), norm_pos_iff.mpr ( add_eq_zero_iff_eq_neg.not.mpr hw2 ) ⟩;
        have := norm_add_sq_real w u; have := norm_sub_sq_real w u; simp_all +decide [ real_inner_comm ] ;
        exact abs_lt.mpr ⟨ by nlinarith [ norm_pos_iff.mpr h_abs.1, norm_pos_iff.mpr h_abs.2 ], by nlinarith [ norm_pos_iff.mpr h_abs.1, norm_pos_iff.mpr h_abs.2 ] ⟩;
      simp_all +decide [ real_inner_comm ];
      nlinarith [ abs_lt.mp h_abs, mul_le_mul_of_nonneg_left hwu hc.1.le ]
