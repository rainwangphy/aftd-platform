import AFTD.Prelude
import AFTD.Kb.Tcs.Support
import AFTD.Kb.Tcs.C

/-!
# prime_convolution_two_support_orbit_formula

Topic: quantum   Node: dfef624bd90e

Provenance: helper lemma. OP-2466 two-support product orbit computation 42733

The product orbit supported at 0 and minus one produces the two-level rank-one environment plus its two crossed diagonal entries, provided the four offsets are distinct and the indicated doubled difference is nonzero.
-/

open Fin.CommRing
set_option maxHeartbeats 1000000
set_option linter.all false

variable {F : Type*} [CommRing F] [Nontrivial F] [DecidableEq F]

def rectP (A B : ℝ) (j : F) : ℝ :=
  if j=0 then A^2 else if j=1 then B^2 else 0

def rectB (r : F) (A B : ℝ) (j : F) : ℝ :=
  if j=0 then A else if j=1-r then B else 0

-- Case j=l: the four distinct offsets are 0, 1, r, 1-r.
theorem rect_twirl_diagonal (r : F) (hr0 : r ≠ 0) (hr1 : r ≠ 1)
    (hr2 : 2*r ≠ 1) (A B : ℝ) (j : F) :
    A^2 * rectB r A B j ^2 + B^2 * rectB r A B (j-r)^2 =
      rectP A B j ^2 + A^2*B^2 * (if j=r ∨ j=1-r then 1 else 0) := by
  have hr1r : r ≠ 1-r := by intro h; apply hr2; linear_combination h
  have hr10 : 1-r ≠ 0 := by intro h; apply hr1; linear_combination -h
  have hr11 : 1-r ≠ 1 := by intro h; apply hr0; linear_combination -h
  have e0 : j-r=0 ↔ j=r := sub_eq_zero
  have e1 : j-r=1-r ↔ j=1 := by constructor <;> intro h <;> linear_combination h
  simp only [rectB, rectP, e0, e1]
  by_cases h0 : j=0
  · subst j; simp [hr0, hr1, hr2, hr10, hr11, hr1r, Ne.symm hr0, Ne.symm hr10] <;> ring
  · by_cases h1 : j=1
    · subst j; simp [hr0, hr1, hr2, hr10, hr11, hr1r, Ne.symm hr1, Ne.symm hr11] <;> ring
    · by_cases h2 : j=r
      · subst j; simp [h0,h1,hr0,hr1,hr1r,hr10,hr11] <;> ring
      · by_cases h3 : j=1-r
        · subst j; simp [h0,h1,h2,hr0,hr1,hr1r,hr10,hr11, Ne.symm hr1r]
        · simp [h0,h1,h2,h3]

-- The only overlapping translates of the two-support orbit occur at j=0.
theorem rect_B_overlap (r : F) (hr1 : r ≠ 1) (hdouble : 2*(1-r) ≠ 0)
    (A B : ℝ) (j : F) :
    rectB r A B j * rectB r A B (j+1-r) = if j=0 then A*B else 0 := by
  have hr10 : 1-r ≠ 0 := by intro h; apply hr1; linear_combination -h
  have ht0 : (1-r)+(1-r) ≠ 0 := by
    intro h
    apply hdouble
    linear_combination h
  have hts : (1-r)+(1-r) ≠ 1-r := by
    intro h; apply hr10; linear_combination h
  by_cases h0 : j=0
  · subst j
    simp [rectB, hr10]
  · by_cases h1 : j=1-r
    · subst j
      have heq : (1-r)+1-r = (1-r)+(1-r) := by ring
      rw [heq]
      simp [rectB, hr10, ht0, hts]
    · simp [rectB, h0, h1]

theorem rect_P_overlap (htwo : (2 : F) ≠ 0) (A B : ℝ) (j : F) :
    rectP A B j * rectP A B (j+1) = if j=0 then A^2*B^2 else 0 := by
  by_cases h0 : j=0
  · subst j
    simp [rectP]
  · by_cases h1 : j=1
    · subst j
      have h21 : (1 : F)+1 ≠ 1 := by
        intro h
        have hh : (1 : F)=0 := by linear_combination h
        exact one_ne_zero hh
      have h20 : (1 : F)+1 ≠ 0 := by intro h; apply htwo; linear_combination h
      simp [rectP, h20, h21]
    · simp [rectP, h0, h1]

def rectA (A B : ℝ) (j : F) : ℝ :=
  if j=0 then A else if j= -1 then B else 0

theorem rect_twirl_algebra (r : F) (hr0 : r ≠ 0) (hr1 : r ≠ 1)
    (hr2 : 2*r ≠ 1) (htwo : (2 : F) ≠ 0) (hdouble : 2*(1-r) ≠ 0) (A B : ℝ) (j l : F) :
    A * rectB r A B j * rectA A B (j-l) * rectB r A B (r*(j-l)+l) +
    B * rectB r A B (j-r) * rectA A B (j-l-1) * rectB r A B (r*(j-l-1)+l) =
      rectP A B j * rectP A B l +
        A^2*B^2 * (if j=l ∧ (j=r ∨ j=1-r) then 1 else 0) := by
  have hneg : (-1 : F) ≠ 0 := neg_ne_zero.mpr one_ne_zero
  have htwo' : (1 : F) ≠ -1 := by intro h; apply htwo; linear_combination h
  have hm2 : (-1 : F) - 1 ≠ 0 := by intro h; apply htwo; linear_combination -h
  have hm21 : (-1 : F) - 1 ≠ -1 := by
    intro h
    have hh : (1 : F) = 0 := by linear_combination -h
    exact one_ne_zero hh
  by_cases h0 : j=l
  · subst l
    simp only [sub_self, mul_zero, zero_add, zero_sub, rectA, if_pos rfl, hneg, if_false, true_and]
    simp only [if_true]
    have he : r * (-1) + j = j-r := by ring
    rw [he]
    have hd := rect_twirl_diagonal r hr0 hr1 hr2 A B j
    nlinarith [hd]
  · by_cases hp : j-l=1
    · have hj : j=l+1 := by linear_combination hp
      subst j
      have hl : l+1 ≠ l := by
        intro h
        have hh : (1 : F) = 0 := by linear_combination h
        exact one_ne_zero hh
      simp only [add_sub_cancel_left, rectA, one_ne_zero, htwo', if_false, sub_self, if_pos rfl,
        mul_zero, zero_add, hl, false_and, ↓reduceIte, mul_zero, add_zero]
      have hb := rect_B_overlap r hr1 hdouble A B l
      have hc := rect_P_overlap htwo A B l
      by_cases hz : l = 0
      · simp only [if_pos hz] at hb hc
        linear_combination (A*B)*hb - hc
      · simp only [if_neg hz] at hb hc
        linear_combination (A*B)*hb - hc
    · by_cases hm : j-l= -1
      · have hl : l=j+1 := by linear_combination -hm
        subst l
        have hj : j ≠ j+1 := by
          intro h
          have hh : (1 : F) = 0 := by linear_combination -h
          exact one_ne_zero hh
        have he : j-(j+1) = (-1 : F) := by ring
        rw [he]
        simp only [rectA, hneg, if_false, if_pos rfl,
          hm2, hm21, mul_zero, zero_add, hj, false_and, ↓reduceIte, add_zero]
        have hb := rect_B_overlap r hr1 hdouble A B j
        have hc := rect_P_overlap htwo A B j
        have hzarg : r*(-1)+(j+1) = j+1-r := by ring
        rw [hzarg]
        by_cases hz : j = 0
        · simp only [if_pos hz] at hb hc
          linear_combination (A*B)*hb - hc
        · simp only [if_neg hz] at hb hc
          linear_combination (A*B)*hb - hc
      · have hsub0 : j-l ≠ 0 := sub_ne_zero.mpr h0
        have hsub10 : j-l-1 ≠ 0 := by intro h; apply hp; linear_combination h
        have hsub1n : j-l-1 ≠ -1 := by intro h; apply hsub0; linear_combination h
        have hP : rectP A B j * rectP A B l = 0 := by
          simp only [rectP]
          split_ifs with a b c d <;> simp_all <;> try ring
          all_goals exfalso <;> first | apply hp | apply hm | apply h0 <;> linear_combination a + b
        simp [rectA, hsub0, hm, hsub10, hsub1n, h0, hP]

open Fin.CommRing
def in1249_A (n : ℕ) (A B : ℝ) (i : Fin (n+2)) : ℝ :=
  if i = 0 then A else if i = -1 then B else 0

def in1249_B (n : ℕ) (r : Fin (n+2)) (A B : ℝ) (i : Fin (n+2)) : ℝ :=
  if i = 0 then A else if i = 1-r then B else 0

def in1249_P (n : ℕ) (A B : ℝ) (i : Fin (n+2)) : ℝ :=
  if i = 0 then A^2 else if i = 1 then B^2 else 0

theorem in1249_twirl_support (n : ℕ) (r : Fin (n+2)) (A B : ℝ)
    (j l : Fin (n+2)) :
    (∑ i, in1249_A n A B i * in1249_B n r A B (r*i+j) *
      in1249_A n A B (i+j-l) * in1249_B n r A B (r*(i+j-l)+l)) =
    A * in1249_B n r A B j * in1249_A n A B (j-l) * in1249_B n r A B (r*(j-l)+l) +
    B * in1249_B n r A B (j-r) * in1249_A n A B (j-l-1) * in1249_B n r A B (r*(j-l-1)+l) := by
  have h01 : (0 : Fin (n+2)) ≠ -1 := by
    intro h
    have h1 : (1 : Fin (n+2)) = 0 := by linear_combination h
    have h1v : ((1 : Fin (n+2)) : ℕ) = 1 := by simp
    rw [h1] at h1v
    simp at h1v
  rw [Fintype.sum_eq_add 0 (-1) h01]
  · have h10 : (-1 : Fin (n+2)) ≠ 0 := Ne.symm h01
    simp only [in1249_A, if_pos rfl, h01, h10, if_false, if_true]
    congr 1 <;> congr 1 <;> congr 1 <;> try ring
  · intro i ⟨hi0, hi1⟩
    simp [in1249_A, hi0, hi1]

theorem prime_convolution_two_support_orbit_formula (n : ℕ) (r : Fin (n+2))
    (hr0 : r ≠ 0) (hr1 : r ≠ 1) (hr2 : 2*r ≠ 1)
    (htwo : (2 : Fin (n+2)) ≠ 0) (hdouble : 2*(1-r) ≠ 0)
    (A B : ℝ) (j l : Fin (n+2)) :
    (∑ i, in1249_A n A B i * in1249_B n r A B (r*i+j) *
      in1249_A n A B (i+j-l) * in1249_B n r A B (r*(i+j-l)+l)) =
      in1249_P n A B j * in1249_P n A B l +
        A^2*B^2 * (if j=l ∧ (j=r ∨ j=1-r) then 1 else 0) := by
  rw [in1249_twirl_support]
  exact rect_twirl_algebra r hr0 hr1 hr2 htwo hdouble A B j l
