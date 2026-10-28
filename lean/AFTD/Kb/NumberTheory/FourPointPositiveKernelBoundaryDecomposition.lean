import AFTD.Prelude
import AFTD.Kb.NumberTheory.IntegerPositiveLineBoundaryDecomposition
import AFTD.Kb.NumberTheory.FourPointPositiveKernelMixedDirection

/-!
# four_point_positive_kernel_boundary_decomposition

Topic: elementary_number_theory   Node: 1c4e0d4f4301

Provenance: helper lemma. Supporting lemma or explicit route obstruction for OP-197 / arXiv:2610.16562 Conjecture1, deep session2. The abstract two-ray fact and finite obstruction are not claimed novel or research-level; no part is the full box conjecture. The five-point kernel has columns (1,1),(1,0),(0,1),(-2,0),(0,-2).

For two integer rows on four coordinates with independent first two columns and a strictly positive integer common kernel vector x, there are two nonzero nonnegative integer common kernel vectors u,v, each having a zero coordinate, and positive integer D,c,d (represented in Z) such that D*x=c*u+d*v. The two vectors are not asserted primitive in this lemma.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem four_point_positive_kernel_boundary_decomposition
    (a b x : Fin 4 → ℤ) (hx : ∀ i, 0 < x i)
    (hxa : (∑ i, x i*a i) = 0) (hxb : (∑ i, x i*b i) = 0)
    (hind : a 0*b 1 - a 1*b 0 ≠ 0) :
    ∃ (u v : Fin 4 → ℤ) (i j : Fin 4) (D c d : ℤ),
      (∀ k, 0 ≤ u k) ∧ (∀ k, 0 ≤ v k) ∧ u ≠ 0 ∧ v ≠ 0 ∧
      u i = 0 ∧ v j = 0 ∧ 0 < D ∧ 0 < c ∧ 0 < d ∧
      (∀ k, D*x k = c*u k + d*v k) ∧
      (∑ k, u k*a k) = 0 ∧ (∑ k, u k*b k) = 0 ∧
      (∑ k, v k*a k) = 0 ∧ (∑ k, v k*b k) = 0 := by
  obtain ⟨w,hsw,hwa,hwb,hp,hn⟩ := four_point_positive_kernel_mixed_direction a b x hx hxa hxb hind
  obtain ⟨u,v,i,j,D,c,d,hu,hv,hun,hvn,hui,hvj,hD,hc,hd,hrel,hue,hve⟩ :=
    integer_positive_line_boundary_decomposition x w hx hp hn
  have hsum (r : Fin 4 → ℤ) (hxr : (∑ k, x k*r k)=0) (hwr : (∑ k, w k*r k)=0)
      (p q : ℤ) : (∑ k, (p*x k-q*w k)*r k)=0 := by
    calc
      _ = p*(∑ k, x k*r k)-q*(∑ k, w k*r k) := by
        simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro k hk; ring
      _ = 0 := by rw [hxr,hwr]; ring
  refine ⟨u,v,i,j,D,c,d,hu,hv,hun,hvn,hui,hvj,hD,hc,hd,hrel,?_,?_,?_,?_⟩
  · rw [hue]; exact hsum a hxa hwa (w i) (x i)
  · rw [hue]; exact hsum b hxb hwb (w i) (x i)
  · rw [hve]
    have he := hsum a hxa hwa (w j) (x j)
    have hn : (∑ k, (x j*w k-w j*x k)*a k) = -(∑ k, (w j*x k-x j*w k)*a k) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro k hk; ring
    rw [hn,he]; ring
  · rw [hve]
    have he := hsum b hxb hwb (w j) (x j)
    have hn : (∑ k, (x j*w k-w j*x k)*b k) = -(∑ k, (w j*x k-x j*w k)*b k) := by
      rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro k hk; ring
    rw [hn,he]; ring
