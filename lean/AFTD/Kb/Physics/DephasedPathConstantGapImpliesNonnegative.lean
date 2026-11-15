import AFTD.Prelude
import AFTD.Kb.Physics.DephasedPathBinaryWeight
import AFTD.Kb.Physics.DephasedPathIntervalPolynomial
import AFTD.Kb.Physics.DephasedPathIntervalBinaryAverage

/-!
# dephased_path_constant_gap_implies_nonnegative

Topic: quantum_mechanics   Node: 861478ba9104

Provenance: helper lemma. binary averaging reduction for the OP-827 path inequality.

A binary constant-gap certificate implies the continuous path inequality under the local noise inequalities.
-/

set_option maxHeartbeats 2000000

open scoped Classical BigOperators in
theorem dephased_path_constant_gap_implies_nonnegative (n : ℕ) (color : Fin n → Fin 4) (left right : Finset (Fin 4)) (q : Fin n → ℝ) (hq : ∀ i, q i ∈ Set.Icc (0 : ℝ) 1) (hlocal : ∀ i j k : Fin n, i.val + 1 = j.val → j.val + 1 = k.val → q j ≥ q i * q k) (E : Finset (Fin n)) (hE : ∀ i ∈ E, 0 < i.val ∧ i.val + 1 < n) (hcert : ∀ P : Finset (Fin n), (∑ i ∈ E, (dephased_path_binary_weight n P i.val - dephased_path_binary_weight n P (i.val - 1) * dephased_path_binary_weight n P (i.val + 1))) ≤ dephased_path_interval_polynomial n color left right (fun i => if i ∈ P then 1 else 0)) : 0 ≤ dephased_path_interval_polynomial n color left right q := by
  classical
  let W (f : Fin n → Bool) : ℝ := ∏ i : Fin n, if f i then q i else 1 - q i
  let B (f : Fin n → Bool) (i : Fin n) : ℝ := if f i then 1 else 0
  let P (f : Fin n → Bool) : Finset (Fin n) := Finset.univ.filter (fun i => f i)
  have hW (f : Fin n → Bool) : 0 ≤ W f := by
    apply Finset.prod_nonneg
    intro i hi
    split <;> have := hq i <;> simp_all [Set.mem_Icc] <;> linarith
  have hB (f : Fin n → Bool) (i : Fin n) :
      dephased_path_binary_weight n (P f) i.val = B f i := by
    unfold dephased_path_binary_weight B
    have hh : (∃ j ∈ P f, j.val = i.val) ↔ f i = true := by
      constructor
      · rintro ⟨j,hj,hji⟩
        have : j = i := Fin.ext hji
        subst j
        simpa [P] using hj
      · intro hi
        exact ⟨i, by simp [P, hi], rfl⟩
    by_cases hf : f i = true
    · have he := hh.mpr hf
      simp [he, hf]
    · have he : ¬ ∃ j ∈ P f, j.val = i.val := fun hx => hf (hh.mp hx)
      simp [he, hf]
  have hm (X : Finset (Fin n)) :
      (∑ f : Fin n → Bool, W f * ∏ i ∈ X, B f i) = ∏ i ∈ X, q i := by
    simpa only [Finset.prod_mul_distrib, Fintype.prod_ite_mem, W, B] using
      independent_binary_monomial_average_work q X
  have h1 (i : Fin n) : (∑ f : Fin n → Bool, W f * B f i) = q i := by
    simpa using hm {i}
  have h2 (i j : Fin n) (hij : i ≠ j) :
      (∑ f : Fin n → Bool, W f * (B f i * B f j)) = q i * q j := by
    simpa [hij] using hm {i,j}
  have hlocalavg (j : Fin n) (hj : j ∈ E) :
      0 ≤ ∑ f : Fin n → Bool, W f *
        (dephased_path_binary_weight n (P f) j.val -
          dephased_path_binary_weight n (P f) (j.val - 1) *
          dephased_path_binary_weight n (P f) (j.val + 1)) := by
    have hj' := hE j hj
    let l : Fin n := ⟨j.val - 1, by omega⟩
    let r : Fin n := ⟨j.val + 1, by omega⟩
    have hl : l.val + 1 = j.val := by dsimp [l]; omega
    have hr : j.val + 1 = r.val := rfl
    have hlr : l ≠ r := by intro h; have := congrArg Fin.val h; dsimp [l,r] at this; omega
    have hlval : l.val = j.val - 1 := rfl
    have hrval : r.val = j.val + 1 := rfl
    have hbl (f : Fin n → Bool) : dephased_path_binary_weight n (P f) (j.val - 1) = B f l := by
      simpa only [hlval] using hB f l
    have hbr (f : Fin n → Bool) : dephased_path_binary_weight n (P f) (j.val + 1) = B f r := by
      simpa only [hrval] using hB f r
    simp_rw [hB, hbl, hbr, mul_sub, Finset.sum_sub_distrib, h1, h2 l r hlr]
    exact sub_nonneg.mpr (hlocal l j r hl hr)
  have hnonneg : 0 ≤ ∑ f : Fin n → Bool, W f *
      ∑ i ∈ E, (dephased_path_binary_weight n (P f) i.val -
        dephased_path_binary_weight n (P f) (i.val - 1) *
        dephased_path_binary_weight n (P f) (i.val + 1)) := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_nonneg (fun i hi => hlocalavg i hi)
  rw [← dephased_path_interval_binary_average n color left right q]
  apply le_trans hnonneg
  apply Finset.sum_le_sum
  intro f hf
  apply mul_le_mul_of_nonneg_left _ (hW f)
  simpa [P] using hcert (P f)
