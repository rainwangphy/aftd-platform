import AFTD.Prelude
import AFTD.Kb.Tcs.CodingTheoryJohnsonBitVec
import AFTD.Kb.Tcs.CodingTheoryJohnsonEuc
import AFTD.Kb.Tcs.CodingTheoryJohnsonHdist
import AFTD.Kb.Tcs.CodingTheoryJohnsonInnerShiftedLeExpr
import AFTD.Kb.Tcs.CodingTheoryJohnsonNormalize
import AFTD.Kb.Tcs.CodingTheoryJohnsonRankinFinsetBound
import AFTD.Kb.Tcs.CodingTheoryJohnsonShifted
import AFTD.Kb.Tcs.CodingTheoryJohnsonWt
import AFTD.Kb.Tcs.CodingTheoryJohnsonPmOneApplyFalse
import AFTD.Kb.Tcs.CodingTheoryJohnsonPmOneApplyTrue
import AFTD.Kb.Tcs.Wt

/-!
# CodingTheory.Johnson.binary_johnson_card_bound_parametric

Topic: information   Node: 495832a68c02

Provenance: helper lemma. TCSlib, `CodingTheory.Johnson.binary_johnson_card_bound_parametric`. Lean proof by Allan Li, Frederick Dehmel, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/JohnsonBound.lean (Apache-2.0); 1 verbatim; compiled here.

Johnson cardinality bound, parametric form. Let $n \ge 1$, let $d, w$ be natural numbers, and let $C$ be a finite set of binary
words of length $n$ such that any two distinct words of $C$ are at Hamming distance at
least $d$, and every word of $C$ has weight at most $w$. Suppose $\alpha \ge 0$ is a
real parameter for which the shifted $\pm 1$ vector $\hat{x}^\alpha$ is nonzero for
every $x \in C$, and for which
\[
(n - 2d) + \alpha^2 n + 2\alpha(2w - n) \le 0 .
\]
Then $\abs{C} \le 2n$.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open scoped BigOperators RealInnerProductSpace in
open Finset in
open Classical in
open scoped RealInnerProductSpace in
open scoped InnerProductSpace in
open Finset in
theorem CodingTheory.Johnson.binary_johnson_card_bound_parametric
    {n d w : ℕ}
    (_hn : 0 < n)
    (C : Finset (BitVec n))
    (hpair : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → d ≤ hdist x y)
    (hwt : ∀ x ∈ C, wt x ≤ w)
    (α : ℝ)
    (hα : 0 ≤ α)
    (hnonzero : ∀ x ∈ C, shifted α x ≠ 0)
    (harith :
      ((n : ℝ) - 2 * (d : ℝ))
        + α^2 * (n : ℝ)
        + 2 * α * (2 * (w : ℝ) - (n : ℝ))
        ≤ 0) :
    C.card ≤ 2 * n := by
  classical
  let u : BitVec n → Euc n := fun x => shifted α x

  have hpair_u :
      ∀ x ∈ C, ∀ y ∈ C, x ≠ y → ⟪u x, u y⟫_[ℝ] ≤ 0 := by
    intro x hx y hy hxy
    have hdist_xy : d ≤ hdist x y := hpair x hx y hy hxy
    have hwt_x : wt x ≤ w := hwt x hx
    have hwt_y : wt y ≤ w := hwt y hy
    have h1 :
        ⟪u x, u y⟫_[ℝ]
          ≤ ((n : ℝ) - 2 * (d : ℝ))
            + α^2 * (n : ℝ)
            + 2 * α * (2 * (w : ℝ) - (n : ℝ)) := by
      simpa [u] using
        (inner_shifted_le_expr (n := n) (d := d) (w := w) (α := α)
      (x := x) (y := y) hα hdist_xy hwt_x hwt_y)
    linarith

  let U : Finset (Euc n) := C.image (fun x => normalize (u x))

  have h_injOn :
      Set.InjOn (fun x : BitVec n => normalize (u x)) (↑C : Set (BitVec n)) := by
    intro x hx y hy; have := hnonzero x hx; have := hnonzero y hy; simp_all +decide [ normalize ] ;
    intro h_eq; specialize hpair_u x hx y hy; contrapose! hpair_u; simp_all +decide [ RCLike.wInner ] ;
    -- Since $u x = ‖u x‖ • ‖u y‖⁻¹ • u y$, we can substitute this into the inner product.
    have h_inner : ∑ i, u y i * u x i = ‖u x‖ * ‖u y‖⁻¹ * ∑ i, u y i * u y i := by
      have h_inner : u x = ‖u x‖ • ‖u y‖⁻¹ • u y := by
        rw [ ← h_eq, smul_smul, mul_inv_cancel₀ ( norm_ne_zero_iff.mpr ( hnonzero x hx ) ), one_smul ];
      conv_lhs => rw [ h_inner ] ; simp +decide [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] ;
      simp +decide only [Finset.mul_sum _ _ _, mul_comm, mul_assoc];
    rw [ h_inner ];
    refine' mul_pos ( mul_pos ( norm_pos_iff.mpr ( hnonzero x hx ) ) ( inv_pos.mpr ( norm_pos_iff.mpr ( hnonzero y hy ) ) ) ) ( lt_of_le_of_ne ( Finset.sum_nonneg fun _ _ => mul_self_nonneg _ ) ( Ne.symm _ ) ) ; intro H ; simp_all +decide [ Finset.sum_eq_zero_iff_of_nonneg, mul_self_nonneg ] ;
    exact hnonzero y hy ( PiLp.ext H )

  have hcardU : U.card = C.card := by
    unfold U
    exact Finset.card_image_of_injOn h_injOn

  have hunitU : ∀ z ∈ U, ‖z‖ = 1 := by
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨x, hxC, rfl⟩
    have hx0 : u x ≠ 0 := hnonzero x hxC
    simp [normalize];
    -- The norm of a scalar multiple of a vector is the absolute value of the scalar times the norm of the vector
    simp [norm_smul, hx0]

  have hpairU : ∀ a ∈ U, ∀ b ∈ U, a ≠ b → ⟪a, b⟫_[ℝ] ≤ 0 := by
    intro a ha b hb hab
    rcases Finset.mem_image.mp ha with ⟨x, hxC, rfl⟩
    rcases Finset.mem_image.mp hb with ⟨y, hyC, rfl⟩
    have hx0 : u x ≠ 0 := hnonzero x hxC
    have hy0 : u y ≠ 0 := hnonzero y hyC
    have hxy : x ≠ y := by
      intro hEq
      apply hab
      simp [normalize, hEq]
    have hbase : ⟪u x, u y⟫_[ℝ] ≤ 0 := hpair_u x hxC y hyC hxy
    -- Since the norms are 1 the inner product simplifies to the inner product of the original vectors
    have h_inner_simplified : ⟪normalize (u x), normalize (u y)⟫_[ℝ] = (1 / (‖u x‖ * ‖u y‖)) * ⟪u x, u y⟫_[ℝ] := by
      simp +decide [ normalize, RCLike.wInner ] ; ring_nf;
      simp +decide only [mul_assoc, mul_left_comm, Finset.mul_sum _ _ _];
    exact h_inner_simplified.symm ▸ mul_nonpos_of_nonneg_of_nonpos ( one_div_nonneg.mpr ( mul_nonneg ( norm_nonneg _ ) ( norm_nonneg _ ) ) ) hbase


  have h_rankin : U.card ≤ 2 * n := rankin_finset_bound (n := n) U hunitU hpairU
  simpa [hcardU] using h_rankin
