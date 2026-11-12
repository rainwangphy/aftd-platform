import AFTD.Prelude

/-!
# rank_four_ppt_normal_completion_phase

Topic: quantum   Node: 1d54a972d805

Provenance: helper lemma. Helper for OP-693, using the rank-four PPT source from https://arxiv.org/abs/1405.4502 and the normal-completion context https://arxiv.org/abs/0903.0090.

Two independent real vectors in dimension three admit a phase rotation that makes the normal-completion equation solvable.
-/

open Matrix
open scoped BigOperators Matrix ComplexOrder
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
set_option linter.unusedSimpArgs false
private lemma in767_phaseproof_solve_three_coordinates
    (xi xj xk yi yj yk vi vj vk : ℝ)
    (hd : xi*yj-xj*yi ≠ 0)
    (hv : vk*(xi*yj-xj*yi)+vi*(xj*yk-xk*yj)+vj*(xk*yi-xi*yk)=0) :
    ∃ a b : ℝ, vi+b*xi-a*yi=0 ∧ vj+b*xj-a*yj=0 ∧ vk+b*xk-a*yk=0 := by
  let D : ℝ := xi*yj-xj*yi
  have hD : D ≠ 0 := hd
  refine ⟨(xi*vj-xj*vi)/D, (yi*vj-yj*vi)/D, ?_, ?_, ?_⟩
  · field_simp [hD]
    dsimp [D]
    ring
  · field_simp [hD]
    dsimp [D]
    ring
  · field_simp [hD]
    dsimp [D]
    linear_combination hv

private lemma in767_phaseproof_plane_span_from_cross
    (X Y v : Fin 3 → ℝ) (hn : (X ⨯₃ Y) ≠ 0)
    (hdot : v ⬝ᵥ (X ⨯₃ Y) = 0) :
    ∃ a b : ℝ, ∀ i : Fin 3, v i + b*X i-a*Y i = 0 := by
  have hv : v 0*(X 1*Y 2-X 2*Y 1) + v 1*(X 2*Y 0-X 0*Y 2) +
      v 2*(X 0*Y 1-X 1*Y 0)=0 := by
    simpa [dotProduct, cross_apply, Fin.sum_univ_three] using hdot
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hn
  fin_cases i
  · change (X ⨯₃ Y) 0 ≠ 0 at hi
    have hd : X 1*Y 2-X 2*Y 1 ≠ 0 := by simpa [cross_apply] using hi
    obtain ⟨a,b,h1,h2,h0⟩ := in767_phaseproof_solve_three_coordinates
      (X 1) (X 2) (X 0) (Y 1) (Y 2) (Y 0) (v 1) (v 2) (v 0) hd hv
    refine ⟨a,b,?_⟩
    intro i
    fin_cases i <;> assumption
  · change (X ⨯₃ Y) 1 ≠ 0 at hi
    have hd : X 2*Y 0-X 0*Y 2 ≠ 0 := by simpa [cross_apply] using hi
    have hv' : v 1*(X 2*Y 0-X 0*Y 2) + v 2*(X 0*Y 1-X 1*Y 0) +
        v 0*(X 1*Y 2-X 2*Y 1)=0 := by linear_combination hv
    obtain ⟨a,b,h2,h0,h1⟩ := in767_phaseproof_solve_three_coordinates
      (X 2) (X 0) (X 1) (Y 2) (Y 0) (Y 1) (v 2) (v 0) (v 1) hd hv'
    refine ⟨a,b,?_⟩
    intro i
    fin_cases i <;> assumption
  · change (X ⨯₃ Y) 2 ≠ 0 at hi
    have hd : X 0*Y 1-X 1*Y 0 ≠ 0 := by simpa [cross_apply] using hi
    have hv' : v 2*(X 0*Y 1-X 1*Y 0) + v 0*(X 1*Y 2-X 2*Y 1) +
        v 1*(X 2*Y 0-X 0*Y 2)=0 := by linear_combination hv
    obtain ⟨a,b,h0,h1,h2⟩ := in767_phaseproof_solve_three_coordinates
      (X 0) (X 1) (X 2) (Y 0) (Y 1) (Y 2) (v 0) (v 1) (v 2) hd hv'
    refine ⟨a,b,?_⟩
    intro i
    fin_cases i <;> assumption

private lemma in767_phaseproof_unit_circle_orthogonal (A B : ℝ) :
    ∃ c s : ℝ, c*c+s*s=1 ∧ c*A+s*B=0 := by
  by_cases h : A=0 ∧ B=0
  · refine ⟨1,0,by norm_num,?_⟩
    rcases h with ⟨rfl,rfl⟩
    norm_num
  · have hpos : 0 < A*A+B*B := by
      have hnonneg : 0 ≤ A*A+B*B := by nlinarith [sq_nonneg A, sq_nonneg B]
      by_contra hn
      have ha : A=0 := by nlinarith [sq_nonneg A, sq_nonneg B]
      have hb : B=0 := by nlinarith [sq_nonneg A, sq_nonneg B]
      exact h ⟨ha,hb⟩
    let d : ℝ := Real.sqrt (A*A+B*B)
    have hd : d ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hpos)
    have hs : d*d = A*A+B*B := by
      dsimp [d]
      nlinarith [Real.sq_sqrt (le_of_lt hpos)]
    refine ⟨B/d, -A/d, ?_, ?_⟩
    · field_simp [hd]
      nlinarith [hs]
    · field_simp [hd]
      ring

private lemma in767_phaseproof_phase_completion
    (R S : Matrix (Fin 3) (Fin 3) ℝ) (x y : Fin 3 → ℝ)
    (hli : LinearIndependent ℝ ![x,y]) :
    ∃ c s a b : ℝ, c*c+s*s=1 ∧
      ∀ i : Fin 3, (R.mulVec (fun j => s*x j+c*y j)) i -
        (S.mulVec (fun j => c*x j-s*y j)) i + b*(c*x i-s*y i)-a*(s*x i+c*y i)=0 := by
  let n : Fin 3 → ℝ := x ⨯₃ y
  have hn : n ≠ 0 := crossProduct_ne_zero_iff_linearIndependent.mpr hli
  let A : ℝ := (fun i => (R.mulVec y) i-(S.mulVec x) i) ⬝ᵥ n
  let B : ℝ := (fun i => (R.mulVec x) i+(S.mulVec y) i) ⬝ᵥ n
  obtain ⟨c,s,hunit,horth⟩ := in767_phaseproof_unit_circle_orthogonal A B
  let X : Fin 3 → ℝ := fun i => c*x i-s*y i
  let Y : Fin 3 → ℝ := fun i => s*x i+c*y i
  let v : Fin 3 → ℝ := fun i => (R.mulVec Y) i-(S.mulVec X) i
  have hcross' : X ⨯₃ Y = (c*c+s*s) • (x ⨯₃ y) := by
    ext i
    fin_cases i <;> simp [cross_apply, X, Y] <;> ring
  have hcross : X ⨯₃ Y = n := by simpa [hunit, n] using hcross'
  have hdot' : v ⬝ᵥ n = c*A+s*B := by
    simp [v, X, Y, A, B, Matrix.mulVec, dotProduct, Fin.sum_univ_three]
    ring
  have hdot : v ⬝ᵥ (X ⨯₃ Y) = 0 := by rw [hcross, hdot', horth]
  have hn' : X ⨯₃ Y ≠ 0 := by rw [hcross]; exact hn
  obtain ⟨a,b,hab⟩ := in767_phaseproof_plane_span_from_cross X Y v hn' hdot
  exact ⟨c,s,a,b,hunit,hab⟩

theorem rank_four_ppt_normal_completion_phase :
  ∀ (R S : Matrix (Fin 3) (Fin 3) ℝ) (x y : Fin 3 → ℝ),
    LinearIndependent ℝ ![x, y] →
    ∃ c s a b : ℝ, c*c + s*s = 1 ∧
      ∀ i : Fin 3,
        (R.mulVec (fun j => s*x j + c*y j)) i -
        (S.mulVec (fun j => c*x j - s*y j)) i +
          b*(c*x i - s*y i) - a*(s*x i + c*y i) = 0 := by
  intro R S x y hli
  exact in767_phaseproof_phase_completion R S x y hli
