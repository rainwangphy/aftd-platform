import AFTD.Prelude

/-!
# CommunicationComplexity.Internal.weighted_sum_approx

Topic: communication   Node: 2955379da889

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Internal.weighted_sum_approx`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/NewmanTheorem/PrivateCoinApproximation.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Weighted sum approximation. Let $\alpha$ be a finite type, let $p, q, g : \alpha \to \bbr$, and suppose $0 \le g(a)
\le 1$ for every $a \in \alpha$. Fix a real number $\delta$, and suppose that for every
subset $T \subseteq \alpha$ one has $\sum_{a \in T} p(a) \le \sum_{a \in T} q(a) +
\delta$. Then $\sum_{a} p(a)\,g(a) \le \sum_{a} q(a)\,g(a) + \delta$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open scoped ENNReal in
/-- If p approximates q (∑_{a∈T} p(a) ≤ ∑_{a∈T} q(a) + δ for all T) and g : α → ℝ with 0 ≤ g ≤ 1, then ∑ p(a)*g(a) ≤ ∑ q(a)*g(a) + δ. Used in the product coin approximation. **Proof sketch.** It suffices to show `Σ (p − q)·g ≤ δ`. Split the sum over `A⁺ = {a | q a < p a}` and its complement. On the complement `(p − q)·g ≤ 0` because `g ≥ 0`. On `A⁺`, `(p − q)·g ≤ p − q` because `g ≤ 1`, and `Σ_{A⁺} (p − q) ≤ δ` is the approximation hypothesis applied to `T = A⁺`. -/
lemma CommunicationComplexity.Internal.weighted_sum_approx {α : Type*} [Fintype α]
    (p q : α → ℝ) (g : α → ℝ)
    (hg_nn : ∀ a, 0 ≤ g a) (hg_le1 : ∀ a, g a ≤ 1)
    (hδ : ℝ)
    (happrox : ∀ T : Finset α, ∑ a ∈ T, p a ≤ ∑ a ∈ T, q a + hδ) :
    ∑ a, p a * g a ≤ ∑ a, q a * g a + hδ := by
  -- Split into A⁺ = {a | q a < p a} and complement
  set Apos := Finset.univ.filter (fun a => q a < p a)
  suffices h : ∑ a, (p a - q a) * g a ≤ hδ by
    have : ∑ a, p a * g a - ∑ a, q a * g a = ∑ a, (p a - q a) * g a := by
      rw [← Finset.sum_sub_distrib]; congr 1; ext a; ring
    linarith
  rw [(Finset.sum_filter_add_sum_filter_not Finset.univ (fun a => q a < p a) _).symm]
  -- Complement: (p-q)*g ≤ 0
  have h_neg : ∑ a ∈ Finset.univ.filter (fun a => ¬(q a < p a)),
      (p a - q a) * g a ≤ 0 := Finset.sum_nonpos (fun a ha =>
    mul_nonpos_of_nonpos_of_nonneg (by linarith [(Finset.mem_filter.mp ha).2]) (hg_nn a))
  -- A⁺: (p-q)*g ≤ (p-q) since g ≤ 1
  have h_pos : ∑ a ∈ Apos, (p a - q a) * g a ≤ ∑ a ∈ Apos, (p a - q a) :=
    Finset.sum_le_sum (fun a ha =>
      mul_le_of_le_one_right (by linarith [(Finset.mem_filter.mp ha).2]) (hg_le1 a))
  -- ∑_{A⁺} (p-q) ≤ δ (from happrox applied to A⁺)
  have h_approx : ∑ a ∈ Apos, (p a - q a) ≤ hδ := by
    have := happrox Apos
    have hsub : ∑ a ∈ Apos, (p a - q a) = ∑ a ∈ Apos, p a - ∑ a ∈ Apos, q a := by
      rw [← Finset.sum_sub_distrib]
    linarith [hsub]
  linarith
