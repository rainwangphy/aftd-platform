import AFTD.Prelude

/-!
# three_qubit_axis_minima_can_hide_descent

Topic: quantum   Node: 8e0fdee312e6

Provenance: helper lemma.

For an explicit five-support GHZ-coordinate state, the squared deviation from uniform probabilities is at least its starting value along each of the nine individual local Pauli-axis rotations, but a specified pair of simultaneous rotations lowers it. The numerator inequalities have positive normalization denominators.
-/

namespace GhzAxisSmall
def ix : Fin 9 → Fin 8 → Fin 8 := ![![3, 2, 1, 0, 7, 6, 5, 4],
  ![7, 6, 5, 4, 3, 2, 1, 0],
  ![4, 5, 6, 7, 0, 1, 2, 3],
  ![2, 3, 0, 1, 6, 7, 4, 5],
  ![6, 7, 4, 5, 2, 3, 0, 1],
  ![4, 5, 6, 7, 0, 1, 2, 3],
  ![1, 0, 3, 2, 5, 4, 7, 6],
  ![5, 4, 7, 6, 1, 0, 3, 2],
  ![4, 5, 6, 7, 0, 1, 2, 3]]
def phase : Fin 9 → Fin 8 → ℝ × ℝ := ![![(1, 0), (1, 0), (1, 0), (1, 0), (-1, 0), (-1, 0), (-1, 0), (-1, 0)],
  ![(0, 1), (0, 1), (0, 1), (0, 1), (0, -1), (0, -1), (0, -1), (0, -1)],
  ![(1, 0), (1, 0), (1, 0), (1, 0), (1, 0), (1, 0), (1, 0), (1, 0)],
  ![(1, 0), (1, 0), (1, 0), (1, 0), (1, 0), (1, 0), (1, 0), (1, 0)],
  ![(0, -1), (0, -1), (0, 1), (0, 1), (0, -1), (0, -1), (0, 1), (0, 1)],
  ![(1, 0), (1, 0), (-1, 0), (-1, 0), (1, 0), (1, 0), (-1, 0), (-1, 0)],
  ![(1, 0), (1, 0), (1, 0), (1, 0), (1, 0), (1, 0), (1, 0), (1, 0)],
  ![(0, -1), (0, 1), (0, -1), (0, 1), (0, -1), (0, 1), (0, -1), (0, 1)],
  ![(1, 0), (-1, 0), (1, 0), (-1, 0), (1, 0), (-1, 0), (1, 0), (-1, 0)]]

def z : Fin 8 → ℝ × ℝ := ![(0,0),(0,0),(0,0),(1,0),(1,0),(1,0),(1,0),(0,1)]

def rotate (j : Fin 9) (t : ℝ) (v : Fin 8 → ℝ × ℝ) (i : Fin 8) : ℝ × ℝ :=
  let a := phase j i
  let b := v (ix j i)
  ((v i).1 + t*(a.1*b.2+a.2*b.1), (v i).2 - t*(a.1*b.1-a.2*b.2))

def numerator (v : Fin 8 → ℝ × ℝ) (d : ℝ) : ℝ :=
  ∑ i : Fin 8, (8*((v i).1^2+(v i).2^2)-5*d)^2

end GhzAxisSmall

theorem three_qubit_axis_minima_can_hide_descent :
    (∀ (j : Fin 9) (t : ℝ),
      120*(1+t^2)^2 ≤ GhzAxisSmall.numerator (GhzAxisSmall.rotate j t GhzAxisSmall.z) (1+t^2)) ∧
    GhzAxisSmall.numerator (GhzAxisSmall.rotate 2 (-(1/10)) (GhzAxisSmall.rotate 1 (1/10) GhzAxisSmall.z))
      ((1+(1/10 : ℝ)^2)^2) < 120*(1+(1/10 : ℝ)^2)^4 := by
  constructor
  · intro j t
    fin_cases j <;> simp [GhzAxisSmall.numerator, GhzAxisSmall.rotate, GhzAxisSmall.z,
      GhzAxisSmall.ix, GhzAxisSmall.phase, Fin.sum_univ_succ] <;> nlinarith [sq_nonneg t]
  · have hv : GhzAxisSmall.rotate 2 (-(1/10)) (GhzAxisSmall.rotate 1 (1/10) GhzAxisSmall.z) =
        ![(0,19/100),(1/10,1/10),(1/10,1/10),(1,0),(89/100,0),(1,1/100),(1,1/100),(0,111/100)] := by
      have hz0 : GhzAxisSmall.z 0 = (0, 0) := rfl
      have hz1 : GhzAxisSmall.z 1 = (0, 0) := rfl
      have hz2 : GhzAxisSmall.z 2 = (0, 0) := rfl
      have hz3 : GhzAxisSmall.z 3 = (1, 0) := rfl
      have hz4 : GhzAxisSmall.z 4 = (1, 0) := rfl
      have hz5 : GhzAxisSmall.z 5 = (1, 0) := rfl
      have hz6 : GhzAxisSmall.z 6 = (1, 0) := rfl
      have hz7 : GhzAxisSmall.z 7 = (0, 1) := rfl
      have hi10 : GhzAxisSmall.ix 1 0 = 7 := rfl
      have hp10 : GhzAxisSmall.phase 1 0 = (0, 1) := rfl
      have hi11 : GhzAxisSmall.ix 1 1 = 6 := rfl
      have hp11 : GhzAxisSmall.phase 1 1 = (0, 1) := rfl
      have hi12 : GhzAxisSmall.ix 1 2 = 5 := rfl
      have hp12 : GhzAxisSmall.phase 1 2 = (0, 1) := rfl
      have hi13 : GhzAxisSmall.ix 1 3 = 4 := rfl
      have hp13 : GhzAxisSmall.phase 1 3 = (0, 1) := rfl
      have hi14 : GhzAxisSmall.ix 1 4 = 3 := rfl
      have hp14 : GhzAxisSmall.phase 1 4 = (0, -1) := rfl
      have hi15 : GhzAxisSmall.ix 1 5 = 2 := rfl
      have hp15 : GhzAxisSmall.phase 1 5 = (0, -1) := rfl
      have hi16 : GhzAxisSmall.ix 1 6 = 1 := rfl
      have hp16 : GhzAxisSmall.phase 1 6 = (0, -1) := rfl
      have hi17 : GhzAxisSmall.ix 1 7 = 0 := rfl
      have hp17 : GhzAxisSmall.phase 1 7 = (0, -1) := rfl
      have hi20 : GhzAxisSmall.ix 2 0 = 4 := rfl
      have hp20 : GhzAxisSmall.phase 2 0 = (1, 0) := rfl
      have hi21 : GhzAxisSmall.ix 2 1 = 5 := rfl
      have hp21 : GhzAxisSmall.phase 2 1 = (1, 0) := rfl
      have hi22 : GhzAxisSmall.ix 2 2 = 6 := rfl
      have hp22 : GhzAxisSmall.phase 2 2 = (1, 0) := rfl
      have hi23 : GhzAxisSmall.ix 2 3 = 7 := rfl
      have hp23 : GhzAxisSmall.phase 2 3 = (1, 0) := rfl
      have hi24 : GhzAxisSmall.ix 2 4 = 0 := rfl
      have hp24 : GhzAxisSmall.phase 2 4 = (1, 0) := rfl
      have hi25 : GhzAxisSmall.ix 2 5 = 1 := rfl
      have hp25 : GhzAxisSmall.phase 2 5 = (1, 0) := rfl
      have hi26 : GhzAxisSmall.ix 2 6 = 2 := rfl
      have hp26 : GhzAxisSmall.phase 2 6 = (1, 0) := rfl
      have hi27 : GhzAxisSmall.ix 2 7 = 3 := rfl
      have hp27 : GhzAxisSmall.phase 2 7 = (1, 0) := rfl
      funext i
      fin_cases i <;> simp only [GhzAxisSmall.rotate, hz0, hz1, hz2, hz3, hz4, hz5, hz6, hz7, hi10, hp10, hi11, hp11, hi12, hp12, hi13, hp13, hi14, hp14, hi15, hp15, hi16, hp16, hi17, hp17, hi20, hp20, hi21, hp21, hi22, hp22, hi23, hp23, hi24, hp24, hi25, hp25, hi26, hp26, hi27, hp27] <;> norm_num <;> simp_all <;> norm_num
    rw [hv]
    norm_num [GhzAxisSmall.numerator, Fin.sum_univ_succ]
