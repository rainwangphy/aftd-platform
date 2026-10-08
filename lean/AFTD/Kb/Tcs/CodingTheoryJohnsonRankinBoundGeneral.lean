import AFTD.Prelude
import AFTD.Kb.Tcs.CodingTheoryJohnsonCardFilterAddTwo
import AFTD.Kb.Tcs.CodingTheoryJohnsonFinrankOrthogonalSpanSingleton
import AFTD.Kb.Tcs.CodingTheoryJohnsonNormNormalizedOrthProj
import AFTD.Kb.Tcs.CodingTheoryJohnsonNormalizedOrthProjInjective
import AFTD.Kb.Tcs.CodingTheoryJohnsonNormalizedOrthProjInnerNonpos
import AFTD.Kb.Tcs.CodingTheoryJohnsonOrthProj
import AFTD.Kb.Tcs.CodingTheoryJohnsonOrthProjNeZero
import AFTD.Kb.Tcs.CodingTheoryJohnsonMkProj
import AFTD.Kb.Tcs.CodingTheoryJohnsonMkProjVal
import AFTD.Kb.Tcs.V

/-!
# CodingTheory.Johnson.rankin_bound_general

Topic: information   Node: 0da7e77a5e0d

Provenance: helper lemma. TCSlib, `CodingTheory.Johnson.rankin_bound_general`. Lean proof by Allan Li, Frederick Dehmel, Hydroxyi (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/ErrorCorrectingCodes/JohnsonBound.lean (Apache-2.0); 1 verbatim; compiled here.

Rankin bound in a finite-dimensional space. Let $V$ be a finite-dimensional real inner product space, and let $S$ be a finite set of
vectors in $V$, each of norm $1$, such that any two distinct vectors of $S$ have
non-positive inner product. Then $\abs{S} \le 2 \dim_{\bbr} V$.
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
/-- Rankin's bound: A set of unit vectors with pairwise non-positive inner products in a finite-dimensional real inner product space has at most 2·dim vectors. -/
theorem CodingTheory.Johnson.rankin_bound_general {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V]
    (S : Finset V) (hunit : ∀ u ∈ S, ‖u‖ = 1)
    (hpair : ∀ u ∈ S, ∀ v ∈ S, u ≠ v → inner ℝ u v ≤ 0) :
    S.card ≤ 2 * Module.finrank ℝ V := by
  induction' hd : Module.finrank ℝ V with d ih generalizing V S
  -- Base case: dim = 0
  · rw [Module.finrank_zero_iff] at hd
    suffices S.card = 0 by omega
    rw [Finset.card_eq_zero]
    by_contra hne
    obtain ⟨x, hx⟩ := Finset.nonempty_of_ne_empty hne
    have h0 : x = 0 := Subsingleton.elim x 0
    rw [h0] at hx; have := hunit 0 hx; norm_num at this
  -- Inductive step: dim = d + 1
  · by_cases hne : S.Nonempty
    · obtain ⟨u, hu_mem⟩ := hne
      have hu_norm : ‖u‖ = 1 := hunit u hu_mem
      -- Define the filtered set T and its image T' under the normalized projection
      let T := S.filter (fun v => v ≠ u ∧ v ≠ -u)
      let f := mkProj u hu_norm
      let T' := T.image f
      -- Step 1: S.card ≤ T.card + 2
      have hcard_ST : S.card ≤ T.card + 2 := card_filter_add_two S u hu_mem
      -- Step 2: T'.card = T.card (injectivity of f on T)
      have hcard_TT' : T'.card = T.card := by
        apply Finset.card_image_of_injOn
        intro a ha b hb hab
        by_contra h_ne
        have ha' := (Finset.mem_coe.mp ha)
        have hb' := (Finset.mem_coe.mp hb)
        rw [Finset.mem_filter] at ha' hb'
        have h_eq_val : (‖orthProj u a‖⁻¹ • orthProj u a : V) =
                        ‖orthProj u b‖⁻¹ • orthProj u b :=
          congr_arg Subtype.val hab
        exact normalized_orthProj_injective u a b hu_norm
          (hunit a ha'.1) (hunit b hb'.1)
          (hpair a ha'.1 u hu_mem ha'.2.1)
          (hpair b hb'.1 u hu_mem hb'.2.1)
          (hpair a ha'.1 b hb'.1 h_ne)
          ha'.2.1 ha'.2.2 hb'.2.1 hb'.2.2 h_ne h_eq_val
      -- Step 3: finrank of orthogonal complement
      have h_finrank : Module.finrank ℝ (↑(Submodule.span ℝ {u})ᗮ) = d := by
        have := finrank_orthogonal_span_singleton u hu_norm; omega
      -- Step 4: T' consists of unit vectors
      have hT'_unit : ∀ v ∈ T', ‖(v : V)‖ = 1 := by
        intro v hv
        obtain ⟨w, hw, hwf⟩ := Finset.mem_image.mp hv
        have hw' := Finset.mem_filter.mp hw
        rw [← hwf, mkProj_val]
        exact norm_normalized_orthProj u w hu_norm (hunit w hw'.1) hw'.2.1 hw'.2.2
      -- Step 5: T' has pairwise non-positive inner products
      have hT'_pair : ∀ v ∈ T', ∀ w ∈ T', v ≠ w → inner ℝ (v : V) (w : V) ≤ 0 := by
        intro v hv w hw hvw
        obtain ⟨a, ha, haf⟩ := Finset.mem_image.mp hv
        obtain ⟨b, hb, hbf⟩ := Finset.mem_image.mp hw
        have ha' := Finset.mem_filter.mp ha
        have hb' := Finset.mem_filter.mp hb
        rw [← haf, ← hbf]
        simp only [f, mkProj_val]
        apply normalized_orthProj_inner_nonpos u a b hu_norm
        · exact hpair a ha'.1 b hb'.1 (fun heq => hvw (by rw [← haf, ← hbf, heq]))
        · exact hpair a ha'.1 u hu_mem ha'.2.1
        · exact hpair b hb'.1 u hu_mem hb'.2.1
        · exact orthProj_ne_zero u a hu_norm (hunit a ha'.1) ha'.2.1 ha'.2.2
        · exact orthProj_ne_zero u b hu_norm (hunit b hb'.1) hb'.2.1 hb'.2.2
      -- Step 6: Apply IH to get T'.card ≤ 2 * d
      have hT'_bound : T'.card ≤ 2 * d := h_finrank ▸ ih T' hT'_unit hT'_pair h_finrank
      -- Combine
      linarith
    · have hempty := Finset.not_nonempty_iff_eq_empty.mp hne
      rw [hempty]; simp
