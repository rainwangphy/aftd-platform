import AFTD.Prelude
import AFTD.Kb.NumberTheory.IntegerPositiveLineBoundaryIndices
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# integer_positive_line_boundary_decomposition

Topic: elementary_number_theory   Node: 531d328fb039

Provenance: helper lemma. Supporting lemma or explicit route obstruction for OP-197 / arXiv:2610.16562 Conjecture1, deep session2. The abstract two-ray fact and finite obstruction are not claimed novel or research-level; no part is the full box conjecture. The five-point kernel has columns (1,1),(1,0),(0,1),(-2,0),(0,-2).

For a strictly positive finite integer vector x and a mixed-sign integer direction w, explicit integer vectors u=w(i)x-x(i)w and v=x(j)w-w(j)x are nonnegative and nonzero, with u(i)=0,v(j)=0, and positive integers D,a,b (represented in Z) satisfy D*x=a*u+b*v. The displayed formulas are included in the conclusion.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem integer_positive_line_boundary_decomposition {ι : Type*} [Fintype ι]
    (x w : ι → ℤ) (hx : ∀ k, 0 < x k)
    (hp : ∃ i, 0 < w i) (hn : ∃ j, w j < 0) :
    ∃ (u v : ι → ℤ) (i j : ι) (D a b : ℤ),
      (∀ k, 0 ≤ u k) ∧ (∀ k, 0 ≤ v k) ∧ u ≠ 0 ∧ v ≠ 0 ∧
      u i = 0 ∧ v j = 0 ∧ 0 < D ∧ 0 < a ∧ 0 < b ∧
      (∀ k, D*x k = a*u k + b*v k) ∧
      u = (fun k => w i*x k - x i*w k) ∧
      v = (fun k => x j*w k - w j*x k) := by
  obtain ⟨i,j,hwi,hwj,hui,hvj⟩ := integer_positive_line_boundary_indices x w hx hp hn
  let u := fun k => w i*x k - x i*w k
  let v := fun k => x j*w k - w j*x k
  have hD : 0 < x j*w i - x i*w j := by
    have hh1 := mul_pos (hx j) hwi
    have hh2 := mul_neg_of_pos_of_neg (hx i) hwj
    omega
  have hui0 : u i = 0 := by dsimp [u]; ring
  have hvj0 : v j = 0 := by dsimp [v]; ring
  have huj : u j = x j*w i - x i*w j := by dsimp [u]; ring
  have hvi : v i = x j*w i - x i*w j := by dsimp [v]; ring
  have hun : u ≠ 0 := by intro hh; have hh' := congrFun hh j; simp only [Pi.zero_apply] at hh'; rw [huj] at hh'; omega
  have hvn : v ≠ 0 := by intro hh; have hh' := congrFun hh i; simp only [Pi.zero_apply] at hh'; rw [hvi] at hh'; omega
  refine ⟨u,v,i,j,x j*w i - x i*w j,x j,x i,?_,?_,hun,hvn,hui0,hvj0,hD,hx j,hx i,?_,rfl,rfl⟩
  · intro k; dsimp [u]; have := hui k; nlinarith
  · intro k; dsimp [v]; have := hvj k; nlinarith
  · intro k; dsimp [u,v]; ring
