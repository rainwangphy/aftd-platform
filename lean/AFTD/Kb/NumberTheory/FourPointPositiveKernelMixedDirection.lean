import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# four_point_positive_kernel_mixed_direction

Topic: elementary_number_theory   Node: 3070c708918b

Provenance: helper lemma. Supporting lemma or explicit route obstruction for OP-197 / arXiv:2610.16562 Conjecture1, deep session2. The abstract two-ray fact and finite obstruction are not claimed novel or research-level; no part is the full box conjecture. The five-point kernel has columns (1,1),(1,0),(0,1),(-2,0),(0,-2).

Let a,b be two integer rows on four coordinates and x a strictly positive integer vector annihilated by both rows. If the first two columns have nonzero determinant, then the common integer kernel contains a mixed-sign vector w whose coordinate sum is zero. The two zero row sums and the positive and negative entries are explicit conclusions.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem four_point_positive_kernel_mixed_direction
    (a b x : Fin 4 → ℤ) (hx : ∀ i, 0 < x i)
    (hxa : (∑ i, x i*a i) = 0) (hxb : (∑ i, x i*b i) = 0)
    (hind : a 0*b 1 - a 1*b 0 ≠ 0) :
    ∃ w : Fin 4 → ℤ, (∑ i, w i) = 0 ∧
      (∑ i, w i*a i) = 0 ∧ (∑ i, w i*b i) = 0 ∧
      (∃ i, 0 < w i) ∧ (∃ j, w j < 0) := by
  let c : Fin 4 → ℤ := ![a 1*b 2-a 2*b 1, a 2*b 0-a 0*b 2, a 0*b 1-a 1*b 0, 0]
  have hca : (∑ i, c i*a i) = 0 := by norm_num [Fin.sum_univ_succ,c]; ring
  have hcb : (∑ i, c i*b i) = 0 := by norm_num [Fin.sum_univ_succ,c]; ring
  let T := ∑ i, x i
  let S := ∑ i, c i
  let w := fun i => T*c i-S*x i
  have hT : 0 < T := by
    have h0 := hx 0; have h1 := hx 1; have h2 := hx 2; have h3 := hx 3
    exact Finset.sum_pos (fun k _ => hx k) ⟨0,Finset.mem_univ 0⟩
  have hsw : (∑ i, w i) = 0 := by
    simp only [w, Finset.sum_sub_distrib, ← Finset.mul_sum]
    change T*S-S*T=0
    ring
  have hwa : (∑ i, w i*a i) = 0 := by
    calc
      _ = T*(∑ i, c i*a i)-S*(∑ i, x i*a i) := by
        simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i hi; dsimp [w]; ring
      _ = 0 := by rw [hca,hxa]; ring
  have hwb : (∑ i, w i*b i) = 0 := by
    calc
      _ = T*(∑ i, c i*b i)-S*(∑ i, x i*b i) := by
        simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
        apply Finset.sum_congr rfl
        intro i hi; dsimp [w]; ring
      _ = 0 := by rw [hcb,hxb]; ring
  have hwne : w ≠ 0 := by
    intro hh
    have hh3 := congrFun hh 3
    have hh2 := congrFun hh 2
    change T*0-S*x 3=0 at hh3
    change T*(a 0*b 1-a 1*b 0)-S*x 2=0 at hh2
    have hS : S=0 := by have := hx 3; nlinarith
    rw [hS] at hh2
    simp only [zero_mul,sub_zero] at hh2
    rcases mul_eq_zero.mp hh2 with h | h
    · omega
    · exact hind h
  have hps : ∃ i, 0 < w i := by
    by_contra hh
    push_neg at hh
    have h0 := hh 0; have h1 := hh 1; have h2 := hh 2; have h3 := hh 3
    have hsum := hsw
    change w 0+(w 1+(w 2+(w 3+0)))=0 at hsum
    have heq : w=0 := by
      funext i
      fin_cases i
      · change w 0=0; omega
      · change w 1=0; omega
      · change w 2=0; omega
      · change w 3=0; omega
    exact hwne heq
  have hns : ∃ i, w i < 0 := by
    by_contra hh
    push_neg at hh
    have h0 := hh 0; have h1 := hh 1; have h2 := hh 2; have h3 := hh 3
    have hsum := hsw
    change w 0+(w 1+(w 2+(w 3+0)))=0 at hsum
    have heq : w=0 := by
      funext i
      fin_cases i
      · change w 0=0; omega
      · change w 1=0; omega
      · change w 2=0; omega
      · change w 3=0; omega
    exact hwne heq
  exact ⟨w,hsw,hwa,hwb,hps,hns⟩
