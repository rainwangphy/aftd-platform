import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ProbabilisticSerialPhase
import AFTD.Kb.GameTheoryEconomics.ProbabilisticSerialFractionalAssignment
import AFTD.Kb.GameTheoryEconomics.ProbabilisticSerialLineCost
import AFTD.Kb.GameTheoryEconomics.IsLineDistancePreferenceProfile

/-!
# probabilistic_serial_line_three_agents_le_of_first_choices_20

Topic: social_choice   Node: 1e463e4636ae

Provenance: helper lemma. lemma for probabilistic_serial_line_distortion_le_three_agents (OP-1158, case n = 3)

Lemma for the case n = 3 of OP-1158, for the 36 ranking profiles in which agent 0 ranks item 2 first and item 0 second. For three agents at real positions a_i and three items at real positions b_j, with each agent ranking the items by distance (ties broken arbitrarily), the cost of the probabilistic serial assignment, sum_ij X_ij |a_i - b_j|, is at most 3 times the cost sum_i |a_i - b_sigma(i)| of every perfect matching sigma.
-/

def psl3f201_psPhaseQ (n : ℕ) (pref : Fin n → Equiv.Perm (Fin n))
    (s : (Fin n → ℚ) × (Fin n → Fin n → ℚ)) : (Fin n → ℚ) × (Fin n → Fin n → ℚ) :=
  let eats : Fin n → Fin n → Bool := fun i j =>
    decide (0 < s.1 j ∧ ∀ j', 0 < s.1 j' → (pref i).symm j ≤ (pref i).symm j')
  let cnt : Fin n → ℕ := fun j => (Finset.univ.filter (fun i => eats i j)).card
  let S := Finset.univ.filter (fun j => 0 < cnt j)
  let t : ℚ := if h : S.Nonempty then S.inf' h (fun j => s.1 j / cnt j) else 0
  (fun j => s.1 j - t * cnt j, fun i j => s.2 i j + if eats i j then t else 0)

def psl3f201_psStateCast {n : ℕ} (s : (Fin n → ℚ) × (Fin n → Fin n → ℚ)) :
    (Fin n → ℝ) × (Fin n → Fin n → ℝ) :=
  (fun j => (s.1 j : ℝ), fun i j => (s.2 i j : ℝ))

theorem psl3f201_psPhaseQ_cast (n : ℕ) (pref : Fin n → Equiv.Perm (Fin n))
    (s : (Fin n → ℚ) × (Fin n → Fin n → ℚ)) :
    probabilistic_serial_phase n pref (psl3f201_psStateCast s) = psl3f201_psStateCast (psl3f201_psPhaseQ n pref s) := by
  classical
  have he : ∀ i j, ((0 : ℝ) < (s.1 j : ℝ) ∧ ∀ j', (0 : ℝ) < (s.1 j' : ℝ) →
      (pref i).symm j ≤ (pref i).symm j') ↔
      (decide (0 < s.1 j ∧ ∀ j', 0 < s.1 j' → (pref i).symm j ≤ (pref i).symm j') = true) := by
    intro i j; simp [Rat.cast_pos]
  unfold probabilistic_serial_phase psl3f201_psPhaseQ psl3f201_psStateCast
  simp only [he]
  have hc : ∀ (S : Finset (Fin n)) (h : S.Nonempty) (g : Fin n → ℚ),
      ((S.inf' h g : ℚ) : ℝ) = S.inf' h (fun j => (g j : ℝ)) := fun S h g =>
    Finset.apply_inf'_eq_inf'_comp (f := g) h (fun q : ℚ => (q : ℝ)) (fun x y => Rat.cast_min x y)
  refine Prod.ext ?_ ?_
  · funext j
    simp only
    split_ifs <;> simp only [Rat.cast_sub, Rat.cast_mul, Rat.cast_natCast, hc, Rat.cast_div, Rat.cast_zero]
  · funext i j
    simp only
    split_ifs <;> simp only [Rat.cast_add, Rat.cast_natCast, hc, Rat.cast_div, Rat.cast_zero]

theorem psl3f201_psQ_cast (n : ℕ) (pref : Fin n → Equiv.Perm (Fin n)) (i j : Fin n) :
    probabilistic_serial_fractional_assignment n pref i j =
      (((psl3f201_psPhaseQ n pref)^[n] (fun _ => 1, fun _ _ => 0)).2 i j : ℝ) := by
  have h0 : ((fun _ => (1 : ℝ), fun _ _ => (0 : ℝ)) : (Fin n → ℝ) × (Fin n → Fin n → ℝ)) =
      psl3f201_psStateCast (fun _ => (1 : ℚ), fun _ _ => (0 : ℚ)) := by
    simp [psl3f201_psStateCast]
  have hs : Function.Semiconj psl3f201_psStateCast (psl3f201_psPhaseQ n pref) (probabilistic_serial_phase n pref) :=
    fun s => (psl3f201_psPhaseQ_cast n pref s).symm
  unfold probabilistic_serial_fractional_assignment
  rw [h0, ← hs.iterate_right n]
  rfl

theorem psl3f201_triC (x y z : ℝ) : |x - z| ≤ |x - y| + |y - z| := abs_sub_le x y z
theorem psl3f201_triB (x y z : ℝ) : |x - y| ≤ |x - z| + |y - z| := by
  have := abs_sub_le x z y; rw [abs_sub_comm z y] at this; exact this
theorem psl3f201_triA (x y z : ℝ) : |y - z| ≤ |x - y| + |x - z| := by
  have := abs_sub_le y x z; rw [abs_sub_comm y x] at this; exact this


def psl3f201_PS3P012 : Equiv.Perm (Fin 3) := ⟨![0,1,2], ![0,1,2], by decide, by decide⟩

def psl3f201_PS3P021 : Equiv.Perm (Fin 3) := ⟨![0,2,1], ![0,2,1], by decide, by decide⟩

def psl3f201_PS3P102 : Equiv.Perm (Fin 3) := ⟨![1,0,2], ![1,0,2], by decide, by decide⟩

def psl3f201_PS3P120 : Equiv.Perm (Fin 3) := ⟨![1,2,0], ![2,0,1], by decide, by decide⟩

def psl3f201_PS3P201 : Equiv.Perm (Fin 3) := ⟨![2,0,1], ![1,2,0], by decide, by decide⟩

def psl3f201_PS3P210 : Equiv.Perm (Fin 3) := ⟨![2,1,0], ![2,1,0], by decide, by decide⟩

theorem psl3f201_ps3_perm_cases (σ : Equiv.Perm (Fin 3)) : σ = psl3f201_PS3P012 ∨ σ = psl3f201_PS3P021 ∨ σ = psl3f201_PS3P102 ∨ σ = psl3f201_PS3P120 ∨ σ = psl3f201_PS3P201 ∨ σ = psl3f201_PS3P210 := by
  revert σ; decide

theorem psl3f201_ps3_case_201_012_012 (a b : Fin 3 → ℝ)
    (h : is_line_distance_preference_profile a b ![psl3f201_PS3P201, psl3f201_PS3P012, psl3f201_PS3P012]) (σ : Equiv.Perm (Fin 3)) :
    probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P012, psl3f201_PS3P012] ≤ 3 * ∑ i, |a i - b (σ i)| := by
  have hX : ((psl3f201_psPhaseQ 3 ![psl3f201_PS3P201, psl3f201_PS3P012, psl3f201_PS3P012])^[3] (fun _ => 1, fun _ _ => 0)).2 = ![![(0 : ℚ), (0 : ℚ), (1 : ℚ)], ![(1/2 : ℚ), (1/2 : ℚ), (0 : ℚ)], ![(1/2 : ℚ), (1/2 : ℚ), (0 : ℚ)]] := by decide +kernel
  have e : probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P012, psl3f201_PS3P012] = (1/1 : ℝ) * |a 0 - b 2| + (1/2 : ℝ) * |a 1 - b 0| + (1/2 : ℝ) * |a 1 - b 1| + (1/2 : ℝ) * |a 2 - b 0| + (1/2 : ℝ) * |a 2 - b 1| := by
    unfold probabilistic_serial_line_cost
    simp only [psl3f201_psQ_cast, hX, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    push_cast; ring
  have p00 : |a 0 - b 2| ≤ |a 0 - b 0| := h 0 0 1 (by decide)
  have p01 : |a 0 - b 0| ≤ |a 0 - b 1| := h 0 1 2 (by decide)
  have p10 : |a 1 - b 0| ≤ |a 1 - b 1| := h 1 0 1 (by decide)
  have p11 : |a 1 - b 1| ≤ |a 1 - b 2| := h 1 1 2 (by decide)
  have p20 : |a 2 - b 0| ≤ |a 2 - b 1| := h 2 0 1 (by decide)
  have p21 : |a 2 - b 1| ≤ |a 2 - b 2| := h 2 1 2 (by decide)
  rw [e]
  rcases psl3f201_ps3_perm_cases σ with rfl | rfl | rfl | rfl | rfl | rfl
  · have hc : ∑ i, |a i - b (psl3f201_PS3P012 i)| = |a 0 - b 0| + |a 1 - b 1| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [p00, p10, p20, p21, abs_nonneg (a 0 - b 0), abs_nonneg (a 1 - b 1), abs_nonneg (a 2 - b 2)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P021 i)| = |a 0 - b 0| + |a 1 - b 2| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [p00, p10, p11, p20, abs_nonneg (a 0 - b 0), abs_nonneg (a 1 - b 2), abs_nonneg (a 2 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P102 i)| = |a 0 - b 1| + |a 1 - b 0| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triA (a 0) (b 0) (b 1), psl3f201_triB (a 1) (a 2) (b 0), psl3f201_triC (a 1) (a 2) (b 1), psl3f201_triC (a 1) (b 0) (b 1), p00, p01, p20, p21, abs_nonneg (a 1 - b 0), abs_nonneg (a 0 - b 1), abs_nonneg (a 2 - b 2)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P120 i)| = |a 0 - b 1| + |a 1 - b 2| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triA (a 0) (b 0) (b 1), psl3f201_triA (a 1) (b 0) (b 2), psl3f201_triC (a 2) (b 0) (b 1), psl3f201_triC (a 2) (b 0) (b 2), p00, p01, p10, p11, p21, abs_nonneg (a 2 - b 0), abs_nonneg (a 0 - b 1), abs_nonneg (a 1 - b 2)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P201 i)| = |a 0 - b 2| + |a 1 - b 0| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triB (a 1) (a 2) (b 0), psl3f201_triC (a 1) (a 2) (b 1), p20, abs_nonneg (a 0 - b 2), abs_nonneg (a 1 - b 0), abs_nonneg (a 2 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P210 i)| = |a 0 - b 2| + |a 1 - b 1| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triB (a 1) (a 2) (b 0), psl3f201_triA (a 1) (a 2) (b 1), p10, abs_nonneg (a 0 - b 2), abs_nonneg (a 2 - b 0), abs_nonneg (a 1 - b 1)]

theorem psl3f201_ps3_case_201_012_021 (a b : Fin 3 → ℝ)
    (h : is_line_distance_preference_profile a b ![psl3f201_PS3P201, psl3f201_PS3P012, psl3f201_PS3P021]) (σ : Equiv.Perm (Fin 3)) :
    probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P012, psl3f201_PS3P021] ≤ 3 * ∑ i, |a i - b (σ i)| := by
  have hX : ((psl3f201_psPhaseQ 3 ![psl3f201_PS3P201, psl3f201_PS3P012, psl3f201_PS3P021])^[3] (fun _ => 1, fun _ _ => 0)).2 = ![![(0 : ℚ), (1/4 : ℚ), (3/4 : ℚ)], ![(1/2 : ℚ), (1/2 : ℚ), (0 : ℚ)], ![(1/2 : ℚ), (1/4 : ℚ), (1/4 : ℚ)]] := by decide +kernel
  have e : probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P012, psl3f201_PS3P021] = (1/4 : ℝ) * |a 0 - b 1| + (3/4 : ℝ) * |a 0 - b 2| + (1/2 : ℝ) * |a 1 - b 0| + (1/2 : ℝ) * |a 1 - b 1| + (1/2 : ℝ) * |a 2 - b 0| + (1/4 : ℝ) * |a 2 - b 1| + (1/4 : ℝ) * |a 2 - b 2| := by
    unfold probabilistic_serial_line_cost
    simp only [psl3f201_psQ_cast, hX, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    push_cast; ring
  have p00 : |a 0 - b 2| ≤ |a 0 - b 0| := h 0 0 1 (by decide)
  have p01 : |a 0 - b 0| ≤ |a 0 - b 1| := h 0 1 2 (by decide)
  have p10 : |a 1 - b 0| ≤ |a 1 - b 1| := h 1 0 1 (by decide)
  have p11 : |a 1 - b 1| ≤ |a 1 - b 2| := h 1 1 2 (by decide)
  have p20 : |a 2 - b 0| ≤ |a 2 - b 2| := h 2 0 1 (by decide)
  have p21 : |a 2 - b 2| ≤ |a 2 - b 1| := h 2 1 2 (by decide)
  rw [e]
  rcases psl3f201_ps3_perm_cases σ with rfl | rfl | rfl | rfl | rfl | rfl
  · have hc : ∑ i, |a i - b (psl3f201_PS3P012 i)| = |a 0 - b 0| + |a 1 - b 1| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triC (a 0) (b 0) (b 1), psl3f201_triB (a 1) (a 2) (b 0), psl3f201_triA (a 1) (a 2) (b 1), psl3f201_triA (a 2) (b 0) (b 1), p00, p10, p20, abs_nonneg (a 0 - b 0), abs_nonneg (a 2 - b 0), abs_nonneg (a 1 - b 1), abs_nonneg (a 2 - b 2)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P021 i)| = |a 0 - b 0| + |a 1 - b 2| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triA (a 0) (a 1) (b 0), psl3f201_triC (a 0) (a 1) (b 1), psl3f201_triB (a 0) (a 1) (b 2), psl3f201_triC (a 0) (a 2) (b 1), psl3f201_triB (a 0) (a 2) (b 2), p00, p10, p11, p20, p21, abs_nonneg (a 0 - b 0), abs_nonneg (a 1 - b 2), abs_nonneg (a 2 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P102 i)| = |a 0 - b 1| + |a 1 - b 0| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triC (a 0) (a 1) (b 0), psl3f201_triB (a 0) (a 1) (b 0), psl3f201_triA (a 0) (a 1) (b 1), psl3f201_triB (a 1) (a 2) (b 0), psl3f201_triA (a 1) (a 2) (b 1), psl3f201_triC (a 1) (a 2) (b 2), p00, p01, p11, p20, abs_nonneg (a 0 - b 1), abs_nonneg (a 1 - b 0), abs_nonneg (a 2 - b 2)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P120 i)| = |a 0 - b 1| + |a 1 - b 2| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triA (a 0) (b 0) (b 1), psl3f201_triB (a 1) (a 2) (b 0), psl3f201_triA (a 1) (a 2) (b 2), psl3f201_triC (a 2) (b 0) (b 1), p00, p01, p10, p11, abs_nonneg (a 2 - b 0), abs_nonneg (a 0 - b 1), abs_nonneg (a 1 - b 2)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P201 i)| = |a 0 - b 2| + |a 1 - b 0| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triB (a 0) (b 1) (b 2), psl3f201_triC (a 1) (b 0) (b 1), psl3f201_triA (a 2) (b 0) (b 1), psl3f201_triA (a 2) (b 1) (b 2), p20, p21, abs_nonneg (a 0 - b 2), abs_nonneg (a 1 - b 0), abs_nonneg (a 2 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P210 i)| = |a 0 - b 2| + |a 1 - b 1| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triB (a 0) (b 1) (b 2), psl3f201_triB (a 1) (a 2) (b 0), psl3f201_triA (a 1) (a 2) (b 1), psl3f201_triC (a 1) (b 0) (b 2), psl3f201_triA (a 1) (b 1) (b 2), psl3f201_triA (a 2) (b 0) (b 2), p10, p21, abs_nonneg (a 0 - b 2), abs_nonneg (a 2 - b 0), abs_nonneg (a 1 - b 1)]

theorem psl3f201_ps3_case_201_012_102 (a b : Fin 3 → ℝ)
    (h : is_line_distance_preference_profile a b ![psl3f201_PS3P201, psl3f201_PS3P012, psl3f201_PS3P102]) (σ : Equiv.Perm (Fin 3)) :
    probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P012, psl3f201_PS3P102] ≤ 3 * ∑ i, |a i - b (σ i)| := by
  have hX : ((psl3f201_psPhaseQ 3 ![psl3f201_PS3P201, psl3f201_PS3P012, psl3f201_PS3P102])^[3] (fun _ => 1, fun _ _ => 0)).2 = ![![(0 : ℚ), (0 : ℚ), (1 : ℚ)], ![(1 : ℚ), (0 : ℚ), (0 : ℚ)], ![(0 : ℚ), (1 : ℚ), (0 : ℚ)]] := by decide +kernel
  have e : probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P012, psl3f201_PS3P102] = (1/1 : ℝ) * |a 0 - b 2| + (1/1 : ℝ) * |a 1 - b 0| + (1/1 : ℝ) * |a 2 - b 1| := by
    unfold probabilistic_serial_line_cost
    simp only [psl3f201_psQ_cast, hX, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    push_cast; ring
  have p00 : |a 0 - b 2| ≤ |a 0 - b 0| := h 0 0 1 (by decide)
  have p01 : |a 0 - b 0| ≤ |a 0 - b 1| := h 0 1 2 (by decide)
  have p10 : |a 1 - b 0| ≤ |a 1 - b 1| := h 1 0 1 (by decide)
  have p11 : |a 1 - b 1| ≤ |a 1 - b 2| := h 1 1 2 (by decide)
  have p20 : |a 2 - b 1| ≤ |a 2 - b 0| := h 2 0 1 (by decide)
  have p21 : |a 2 - b 0| ≤ |a 2 - b 2| := h 2 1 2 (by decide)
  rw [e]
  rcases psl3f201_ps3_perm_cases σ with rfl | rfl | rfl | rfl | rfl | rfl
  · have hc : ∑ i, |a i - b (psl3f201_PS3P012 i)| = |a 0 - b 0| + |a 1 - b 1| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [p00, p10, p20, p21, abs_nonneg (a 0 - b 0), abs_nonneg (a 1 - b 1), abs_nonneg (a 2 - b 2)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P021 i)| = |a 0 - b 0| + |a 1 - b 2| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [p00, p10, p11, abs_nonneg (a 0 - b 0), abs_nonneg (a 1 - b 2), abs_nonneg (a 2 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P102 i)| = |a 0 - b 1| + |a 1 - b 0| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [p00, p01, p20, p21, abs_nonneg (a 0 - b 1), abs_nonneg (a 1 - b 0), abs_nonneg (a 2 - b 2)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P120 i)| = |a 0 - b 1| + |a 1 - b 2| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [p00, p01, p10, p11, p20, abs_nonneg (a 0 - b 1), abs_nonneg (a 1 - b 2), abs_nonneg (a 2 - b 0)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P201 i)| = |a 0 - b 2| + |a 1 - b 0| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [abs_nonneg (a 0 - b 2), abs_nonneg (a 1 - b 0), abs_nonneg (a 2 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P210 i)| = |a 0 - b 2| + |a 1 - b 1| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [p10, p20, abs_nonneg (a 0 - b 2), abs_nonneg (a 1 - b 1), abs_nonneg (a 2 - b 0)]

theorem psl3f201_ps3_case_201_012_120 (a b : Fin 3 → ℝ)
    (h : is_line_distance_preference_profile a b ![psl3f201_PS3P201, psl3f201_PS3P012, psl3f201_PS3P120]) (σ : Equiv.Perm (Fin 3)) :
    probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P012, psl3f201_PS3P120] ≤ 3 * ∑ i, |a i - b (σ i)| := by
  have hX : ((psl3f201_psPhaseQ 3 ![psl3f201_PS3P201, psl3f201_PS3P012, psl3f201_PS3P120])^[3] (fun _ => 1, fun _ _ => 0)).2 = ![![(0 : ℚ), (0 : ℚ), (1 : ℚ)], ![(1 : ℚ), (0 : ℚ), (0 : ℚ)], ![(0 : ℚ), (1 : ℚ), (0 : ℚ)]] := by decide +kernel
  have e : probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P012, psl3f201_PS3P120] = (1/1 : ℝ) * |a 0 - b 2| + (1/1 : ℝ) * |a 1 - b 0| + (1/1 : ℝ) * |a 2 - b 1| := by
    unfold probabilistic_serial_line_cost
    simp only [psl3f201_psQ_cast, hX, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    push_cast; ring
  have p00 : |a 0 - b 2| ≤ |a 0 - b 0| := h 0 0 1 (by decide)
  have p01 : |a 0 - b 0| ≤ |a 0 - b 1| := h 0 1 2 (by decide)
  have p10 : |a 1 - b 0| ≤ |a 1 - b 1| := h 1 0 1 (by decide)
  have p11 : |a 1 - b 1| ≤ |a 1 - b 2| := h 1 1 2 (by decide)
  have p20 : |a 2 - b 1| ≤ |a 2 - b 2| := h 2 0 1 (by decide)
  have p21 : |a 2 - b 2| ≤ |a 2 - b 0| := h 2 1 2 (by decide)
  rw [e]
  rcases psl3f201_ps3_perm_cases σ with rfl | rfl | rfl | rfl | rfl | rfl
  · have hc : ∑ i, |a i - b (psl3f201_PS3P012 i)| = |a 0 - b 0| + |a 1 - b 1| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [p00, p10, p20, abs_nonneg (a 0 - b 0), abs_nonneg (a 1 - b 1), abs_nonneg (a 2 - b 2)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P021 i)| = |a 0 - b 0| + |a 1 - b 2| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [p00, p10, p11, abs_nonneg (a 0 - b 0), abs_nonneg (a 1 - b 2), abs_nonneg (a 2 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P102 i)| = |a 0 - b 1| + |a 1 - b 0| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [p00, p01, p20, abs_nonneg (a 0 - b 1), abs_nonneg (a 1 - b 0), abs_nonneg (a 2 - b 2)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P120 i)| = |a 0 - b 1| + |a 1 - b 2| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [p00, p01, p10, p11, p20, p21, abs_nonneg (a 0 - b 1), abs_nonneg (a 1 - b 2), abs_nonneg (a 2 - b 0)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P201 i)| = |a 0 - b 2| + |a 1 - b 0| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [abs_nonneg (a 0 - b 2), abs_nonneg (a 1 - b 0), abs_nonneg (a 2 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P210 i)| = |a 0 - b 2| + |a 1 - b 1| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [p10, p20, p21, abs_nonneg (a 0 - b 2), abs_nonneg (a 1 - b 1), abs_nonneg (a 2 - b 0)]

theorem psl3f201_ps3_case_201_012_201 (a b : Fin 3 → ℝ)
    (h : is_line_distance_preference_profile a b ![psl3f201_PS3P201, psl3f201_PS3P012, psl3f201_PS3P201]) (σ : Equiv.Perm (Fin 3)) :
    probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P012, psl3f201_PS3P201] ≤ 3 * ∑ i, |a i - b (σ i)| := by
  have hX : ((psl3f201_psPhaseQ 3 ![psl3f201_PS3P201, psl3f201_PS3P012, psl3f201_PS3P201])^[3] (fun _ => 1, fun _ _ => 0)).2 = ![![(1/6 : ℚ), (1/3 : ℚ), (1/2 : ℚ)], ![(2/3 : ℚ), (1/3 : ℚ), (0 : ℚ)], ![(1/6 : ℚ), (1/3 : ℚ), (1/2 : ℚ)]] := by decide +kernel
  have e : probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P012, psl3f201_PS3P201] = (1/6 : ℝ) * |a 0 - b 0| + (1/3 : ℝ) * |a 0 - b 1| + (1/2 : ℝ) * |a 0 - b 2| + (2/3 : ℝ) * |a 1 - b 0| + (1/3 : ℝ) * |a 1 - b 1| + (1/6 : ℝ) * |a 2 - b 0| + (1/3 : ℝ) * |a 2 - b 1| + (1/2 : ℝ) * |a 2 - b 2| := by
    unfold probabilistic_serial_line_cost
    simp only [psl3f201_psQ_cast, hX, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    push_cast; ring
  have p00 : |a 0 - b 2| ≤ |a 0 - b 0| := h 0 0 1 (by decide)
  have p01 : |a 0 - b 0| ≤ |a 0 - b 1| := h 0 1 2 (by decide)
  have p10 : |a 1 - b 0| ≤ |a 1 - b 1| := h 1 0 1 (by decide)
  have p11 : |a 1 - b 1| ≤ |a 1 - b 2| := h 1 1 2 (by decide)
  have p20 : |a 2 - b 2| ≤ |a 2 - b 0| := h 2 0 1 (by decide)
  have p21 : |a 2 - b 0| ≤ |a 2 - b 1| := h 2 1 2 (by decide)
  rw [e]
  rcases psl3f201_ps3_perm_cases σ with rfl | rfl | rfl | rfl | rfl | rfl
  · have hc : ∑ i, |a i - b (psl3f201_PS3P012 i)| = |a 0 - b 0| + |a 1 - b 1| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triB (a 0) (a 1) (b 0), psl3f201_triC (a 0) (a 1) (b 1), psl3f201_triC (a 0) (b 0) (b 1), psl3f201_triA (a 0) (b 0) (b 2), psl3f201_triA (a 1) (a 2) (b 1), psl3f201_triB (a 1) (a 2) (b 2), psl3f201_triC (a 1) (b 0) (b 2), psl3f201_triA (a 2) (b 0) (b 1), psl3f201_triB (a 2) (b 0) (b 2), psl3f201_triB (a 2) (b 1) (b 2), psl3f201_triA (a 2) (b 1) (b 2), p00, p10, abs_nonneg (a 0 - b 0), abs_nonneg (a 1 - b 1), abs_nonneg (a 2 - b 2)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P021 i)| = |a 0 - b 0| + |a 1 - b 2| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triA (a 0) (a 1) (b 0), psl3f201_triC (a 0) (a 1) (b 1), psl3f201_triB (a 0) (a 1) (b 2), psl3f201_triC (a 0) (b 0) (b 1), psl3f201_triA (a 2) (b 0) (b 1), p00, p10, p11, p20, p21, abs_nonneg (a 0 - b 0), abs_nonneg (a 1 - b 2), abs_nonneg (a 2 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P102 i)| = |a 0 - b 1| + |a 1 - b 0| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triB (a 0) (a 1) (b 0), psl3f201_triA (a 0) (a 1) (b 2), psl3f201_triA (a 0) (b 1) (b 2), psl3f201_triB (a 2) (b 1) (b 2), p00, p01, p11, p21, abs_nonneg (a 1 - b 0), abs_nonneg (a 2 - b 2), abs_nonneg (a 0 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P120 i)| = |a 0 - b 1| + |a 1 - b 2| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triB (a 0) (a 2) (b 0), psl3f201_triA (a 0) (a 2) (b 1), psl3f201_triA (a 1) (b 0) (b 1), psl3f201_triC (a 2) (b 0) (b 1), p00, p01, p10, p11, p20, abs_nonneg (a 2 - b 2), abs_nonneg (a 0 - b 1), abs_nonneg (a 1 - b 2), abs_nonneg (a 2 - b 0)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P201 i)| = |a 0 - b 2| + |a 1 - b 0| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triC (a 0) (a 2) (b 1), psl3f201_triB (a 0) (a 2) (b 2), psl3f201_triC (a 1) (b 0) (b 1), psl3f201_triA (a 2) (b 0) (b 1), p01, p20, p21, abs_nonneg (a 0 - b 2), abs_nonneg (a 1 - b 0), abs_nonneg (a 2 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P210 i)| = |a 0 - b 2| + |a 1 - b 1| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triB (a 0) (a 1) (b 0), psl3f201_triA (a 0) (a 1) (b 2), psl3f201_triB (a 0) (b 0) (b 2), psl3f201_triB (a 0) (b 1) (b 2), psl3f201_triA (a 0) (b 1) (b 2), psl3f201_triB (a 1) (a 2) (b 0), psl3f201_triA (a 1) (a 2) (b 1), psl3f201_triA (a 1) (b 1) (b 2), psl3f201_triA (a 2) (b 0) (b 2), psl3f201_triB (a 2) (b 1) (b 2), p10, p20, abs_nonneg (a 0 - b 2), abs_nonneg (a 1 - b 1), abs_nonneg (a 2 - b 0)]

theorem psl3f201_ps3_case_201_012_210 (a b : Fin 3 → ℝ)
    (h : is_line_distance_preference_profile a b ![psl3f201_PS3P201, psl3f201_PS3P012, psl3f201_PS3P210]) (σ : Equiv.Perm (Fin 3)) :
    probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P012, psl3f201_PS3P210] ≤ 3 * ∑ i, |a i - b (σ i)| := by
  have hX : ((psl3f201_psPhaseQ 3 ![psl3f201_PS3P201, psl3f201_PS3P012, psl3f201_PS3P210])^[3] (fun _ => 1, fun _ _ => 0)).2 = ![![(1/4 : ℚ), (1/4 : ℚ), (1/2 : ℚ)], ![(3/4 : ℚ), (1/4 : ℚ), (0 : ℚ)], ![(0 : ℚ), (1/2 : ℚ), (1/2 : ℚ)]] := by decide +kernel
  have e : probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P012, psl3f201_PS3P210] = (1/4 : ℝ) * |a 0 - b 0| + (1/4 : ℝ) * |a 0 - b 1| + (1/2 : ℝ) * |a 0 - b 2| + (3/4 : ℝ) * |a 1 - b 0| + (1/4 : ℝ) * |a 1 - b 1| + (1/2 : ℝ) * |a 2 - b 1| + (1/2 : ℝ) * |a 2 - b 2| := by
    unfold probabilistic_serial_line_cost
    simp only [psl3f201_psQ_cast, hX, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    push_cast; ring
  have p00 : |a 0 - b 2| ≤ |a 0 - b 0| := h 0 0 1 (by decide)
  have p01 : |a 0 - b 0| ≤ |a 0 - b 1| := h 0 1 2 (by decide)
  have p10 : |a 1 - b 0| ≤ |a 1 - b 1| := h 1 0 1 (by decide)
  have p11 : |a 1 - b 1| ≤ |a 1 - b 2| := h 1 1 2 (by decide)
  have p20 : |a 2 - b 2| ≤ |a 2 - b 1| := h 2 0 1 (by decide)
  have p21 : |a 2 - b 1| ≤ |a 2 - b 0| := h 2 1 2 (by decide)
  rw [e]
  rcases psl3f201_ps3_perm_cases σ with rfl | rfl | rfl | rfl | rfl | rfl
  · have hc : ∑ i, |a i - b (psl3f201_PS3P012 i)| = |a 0 - b 0| + |a 1 - b 1| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triB (a 0) (a 1) (b 0), psl3f201_triC (a 0) (a 1) (b 1), psl3f201_triA (a 0) (a 2) (b 0), psl3f201_triB (a 0) (a 2) (b 2), psl3f201_triB (a 2) (b 1) (b 2), psl3f201_triA (a 2) (b 1) (b 2), p00, p10, p21, abs_nonneg (a 1 - b 1), abs_nonneg (a 0 - b 0), abs_nonneg (a 2 - b 2)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P021 i)| = |a 0 - b 0| + |a 1 - b 2| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triC (a 0) (a 2) (b 1), psl3f201_triB (a 0) (a 2) (b 2), psl3f201_triC (a 0) (b 0) (b 1), psl3f201_triA (a 1) (b 0) (b 1), p00, p10, p11, p20, abs_nonneg (a 0 - b 0), abs_nonneg (a 1 - b 2), abs_nonneg (a 2 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P102 i)| = |a 0 - b 1| + |a 1 - b 0| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triA (a 0) (b 0) (b 1), psl3f201_triA (a 0) (b 1) (b 2), psl3f201_triC (a 1) (b 0) (b 1), psl3f201_triB (a 2) (b 1) (b 2), p00, p01, abs_nonneg (a 1 - b 0), abs_nonneg (a 2 - b 2), abs_nonneg (a 0 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P120 i)| = |a 0 - b 1| + |a 1 - b 2| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [p00, p01, p10, p11, p20, p21, abs_nonneg (a 0 - b 1), abs_nonneg (a 1 - b 2), abs_nonneg (a 2 - b 0)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P201 i)| = |a 0 - b 2| + |a 1 - b 0| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triB (a 0) (a 1) (b 0), psl3f201_triA (a 0) (a 1) (b 2), psl3f201_triB (a 0) (b 1) (b 2), psl3f201_triA (a 2) (b 1) (b 2), p01, p11, p20, abs_nonneg (a 0 - b 2), abs_nonneg (a 1 - b 0), abs_nonneg (a 2 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P210 i)| = |a 0 - b 2| + |a 1 - b 1| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triB (a 0) (a 1) (b 0), psl3f201_triA (a 0) (a 1) (b 2), psl3f201_triB (a 0) (a 2) (b 2), psl3f201_triA (a 0) (a 2) (b 2), psl3f201_triB (a 0) (b 0) (b 2), psl3f201_triB (a 0) (b 1) (b 2), psl3f201_triB (a 1) (a 2) (b 0), psl3f201_triA (a 1) (a 2) (b 1), psl3f201_triA (a 1) (b 1) (b 2), psl3f201_triA (a 2) (b 0) (b 2), p10, p20, p21, abs_nonneg (a 0 - b 2), abs_nonneg (a 1 - b 1), abs_nonneg (a 2 - b 0)]

theorem psl3f201_ps3_case_201_021_012 (a b : Fin 3 → ℝ)
    (h : is_line_distance_preference_profile a b ![psl3f201_PS3P201, psl3f201_PS3P021, psl3f201_PS3P012]) (σ : Equiv.Perm (Fin 3)) :
    probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P021, psl3f201_PS3P012] ≤ 3 * ∑ i, |a i - b (σ i)| := by
  have hX : ((psl3f201_psPhaseQ 3 ![psl3f201_PS3P201, psl3f201_PS3P021, psl3f201_PS3P012])^[3] (fun _ => 1, fun _ _ => 0)).2 = ![![(0 : ℚ), (1/4 : ℚ), (3/4 : ℚ)], ![(1/2 : ℚ), (1/4 : ℚ), (1/4 : ℚ)], ![(1/2 : ℚ), (1/2 : ℚ), (0 : ℚ)]] := by decide +kernel
  have e : probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P021, psl3f201_PS3P012] = (1/4 : ℝ) * |a 0 - b 1| + (3/4 : ℝ) * |a 0 - b 2| + (1/2 : ℝ) * |a 1 - b 0| + (1/4 : ℝ) * |a 1 - b 1| + (1/4 : ℝ) * |a 1 - b 2| + (1/2 : ℝ) * |a 2 - b 0| + (1/2 : ℝ) * |a 2 - b 1| := by
    unfold probabilistic_serial_line_cost
    simp only [psl3f201_psQ_cast, hX, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    push_cast; ring
  have p00 : |a 0 - b 2| ≤ |a 0 - b 0| := h 0 0 1 (by decide)
  have p01 : |a 0 - b 0| ≤ |a 0 - b 1| := h 0 1 2 (by decide)
  have p10 : |a 1 - b 0| ≤ |a 1 - b 2| := h 1 0 1 (by decide)
  have p11 : |a 1 - b 2| ≤ |a 1 - b 1| := h 1 1 2 (by decide)
  have p20 : |a 2 - b 0| ≤ |a 2 - b 1| := h 2 0 1 (by decide)
  have p21 : |a 2 - b 1| ≤ |a 2 - b 2| := h 2 1 2 (by decide)
  rw [e]
  rcases psl3f201_ps3_perm_cases σ with rfl | rfl | rfl | rfl | rfl | rfl
  · have hc : ∑ i, |a i - b (psl3f201_PS3P012 i)| = |a 0 - b 0| + |a 1 - b 1| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triA (a 0) (a 1) (b 0), psl3f201_triB (a 0) (a 1) (b 2), psl3f201_triC (a 0) (b 0) (b 1), psl3f201_triA (a 1) (b 0) (b 1), psl3f201_triA (a 2) (b 0) (b 1), p00, p10, p11, p20, p21, abs_nonneg (a 0 - b 0), abs_nonneg (a 1 - b 1), abs_nonneg (a 2 - b 2)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P021 i)| = |a 0 - b 0| + |a 1 - b 2| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triC (a 0) (b 0) (b 1), psl3f201_triB (a 1) (a 2) (b 0), psl3f201_triC (a 1) (a 2) (b 1), psl3f201_triA (a 2) (b 0) (b 1), p00, p10, p20, abs_nonneg (a 0 - b 0), abs_nonneg (a 1 - b 2), abs_nonneg (a 2 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P102 i)| = |a 0 - b 1| + |a 1 - b 0| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triB (a 0) (a 1) (b 0), psl3f201_triA (a 0) (a 1) (b 1), psl3f201_triB (a 1) (a 2) (b 0), psl3f201_triC (a 1) (a 2) (b 2), p00, p01, p20, p21, abs_nonneg (a 1 - b 0), abs_nonneg (a 0 - b 1), abs_nonneg (a 2 - b 2)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P120 i)| = |a 0 - b 1| + |a 1 - b 2| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triB (a 0) (a 1) (b 0), psl3f201_triA (a 0) (a 1) (b 1), psl3f201_triA (a 0) (b 0) (b 1), psl3f201_triB (a 1) (a 2) (b 0), psl3f201_triA (a 1) (a 2) (b 2), psl3f201_triC (a 2) (b 0) (b 1), p00, p01, p10, p21, abs_nonneg (a 2 - b 0), abs_nonneg (a 0 - b 1), abs_nonneg (a 1 - b 2)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P201 i)| = |a 0 - b 2| + |a 1 - b 0| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triB (a 0) (b 1) (b 2), psl3f201_triC (a 1) (b 0) (b 1), psl3f201_triA (a 1) (b 0) (b 2), psl3f201_triA (a 2) (b 0) (b 1), psl3f201_triC (a 2) (b 0) (b 2), psl3f201_triA (a 2) (b 1) (b 2), p11, p20, abs_nonneg (a 0 - b 2), abs_nonneg (a 1 - b 0), abs_nonneg (a 2 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P210 i)| = |a 0 - b 2| + |a 1 - b 1| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triB (a 0) (b 1) (b 2), psl3f201_triA (a 1) (b 0) (b 1), psl3f201_triA (a 1) (b 1) (b 2), psl3f201_triC (a 2) (b 0) (b 1), p10, p11, abs_nonneg (a 0 - b 2), abs_nonneg (a 2 - b 0), abs_nonneg (a 1 - b 1)]

theorem psl3f201_ps3_case_201_021_021 (a b : Fin 3 → ℝ)
    (h : is_line_distance_preference_profile a b ![psl3f201_PS3P201, psl3f201_PS3P021, psl3f201_PS3P021]) (σ : Equiv.Perm (Fin 3)) :
    probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P021, psl3f201_PS3P021] ≤ 3 * ∑ i, |a i - b (σ i)| := by
  have hX : ((psl3f201_psPhaseQ 3 ![psl3f201_PS3P201, psl3f201_PS3P021, psl3f201_PS3P021])^[3] (fun _ => 1, fun _ _ => 0)).2 = ![![(0 : ℚ), (1/3 : ℚ), (2/3 : ℚ)], ![(1/2 : ℚ), (1/3 : ℚ), (1/6 : ℚ)], ![(1/2 : ℚ), (1/3 : ℚ), (1/6 : ℚ)]] := by decide +kernel
  have e : probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P021, psl3f201_PS3P021] = (1/3 : ℝ) * |a 0 - b 1| + (2/3 : ℝ) * |a 0 - b 2| + (1/2 : ℝ) * |a 1 - b 0| + (1/3 : ℝ) * |a 1 - b 1| + (1/6 : ℝ) * |a 1 - b 2| + (1/2 : ℝ) * |a 2 - b 0| + (1/3 : ℝ) * |a 2 - b 1| + (1/6 : ℝ) * |a 2 - b 2| := by
    unfold probabilistic_serial_line_cost
    simp only [psl3f201_psQ_cast, hX, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    push_cast; ring
  have p00 : |a 0 - b 2| ≤ |a 0 - b 0| := h 0 0 1 (by decide)
  have p01 : |a 0 - b 0| ≤ |a 0 - b 1| := h 0 1 2 (by decide)
  have p10 : |a 1 - b 0| ≤ |a 1 - b 2| := h 1 0 1 (by decide)
  have p11 : |a 1 - b 2| ≤ |a 1 - b 1| := h 1 1 2 (by decide)
  have p20 : |a 2 - b 0| ≤ |a 2 - b 2| := h 2 0 1 (by decide)
  have p21 : |a 2 - b 2| ≤ |a 2 - b 1| := h 2 1 2 (by decide)
  rw [e]
  rcases psl3f201_ps3_perm_cases σ with rfl | rfl | rfl | rfl | rfl | rfl
  · have hc : ∑ i, |a i - b (psl3f201_PS3P012 i)| = |a 0 - b 0| + |a 1 - b 1| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triC (a 0) (b 0) (b 1), psl3f201_triB (a 1) (a 2) (b 0), psl3f201_triC (a 1) (a 2) (b 2), psl3f201_triA (a 1) (b 0) (b 1), psl3f201_triA (a 1) (b 1) (b 2), psl3f201_triB (a 2) (b 1) (b 2), p00, p10, p11, p20, abs_nonneg (a 0 - b 2), abs_nonneg (a 0 - b 0), abs_nonneg (a 1 - b 1), abs_nonneg (a 2 - b 2)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P021 i)| = |a 0 - b 0| + |a 1 - b 2| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triC (a 0) (a 2) (b 1), psl3f201_triB (a 0) (a 2) (b 2), psl3f201_triC (a 0) (b 0) (b 1), psl3f201_triA (a 0) (b 0) (b 1), psl3f201_triB (a 1) (b 1) (b 2), psl3f201_triA (a 2) (b 1) (b 2), p00, p10, p20, p21, abs_nonneg (a 1 - b 2), abs_nonneg (a 0 - b 0), abs_nonneg (a 2 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P102 i)| = |a 0 - b 1| + |a 1 - b 0| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triB (a 0) (a 1) (b 0), psl3f201_triA (a 0) (a 1) (b 1), psl3f201_triC (a 0) (a 1) (b 2), psl3f201_triA (a 1) (b 0) (b 1), psl3f201_triC (a 1) (b 0) (b 2), psl3f201_triA (a 1) (b 1) (b 2), psl3f201_triC (a 2) (b 0) (b 1), psl3f201_triA (a 2) (b 0) (b 2), psl3f201_triB (b 0) (b 1) (b 2), p00, p01, p20, abs_nonneg (a 0 - b 1), abs_nonneg (a 1 - b 0), abs_nonneg (a 2 - b 2)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P120 i)| = |a 0 - b 1| + |a 1 - b 2| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triA (a 0) (a 1) (b 1), psl3f201_triB (a 0) (a 1) (b 2), psl3f201_triB (a 0) (a 2) (b 0), psl3f201_triA (a 0) (a 2) (b 1), psl3f201_triC (a 1) (b 0) (b 1), psl3f201_triA (a 1) (b 0) (b 1), psl3f201_triA (a 1) (b 0) (b 2), psl3f201_triC (a 2) (b 0) (b 2), psl3f201_triA (a 2) (b 0) (b 2), p00, p01, p10, abs_nonneg (a 0 - b 1), abs_nonneg (a 1 - b 2), abs_nonneg (a 2 - b 0)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P201 i)| = |a 0 - b 2| + |a 1 - b 0| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triC (a 0) (a 2) (b 1), psl3f201_triB (a 0) (a 2) (b 2), psl3f201_triA (a 0) (b 0) (b 2), psl3f201_triC (a 1) (b 0) (b 1), psl3f201_triC (a 1) (b 0) (b 2), psl3f201_triA (a 2) (b 0) (b 1), p01, p20, p21, abs_nonneg (a 0 - b 2), abs_nonneg (a 1 - b 0), abs_nonneg (a 2 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P210 i)| = |a 0 - b 2| + |a 1 - b 1| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triB (a 0) (a 2) (b 0), psl3f201_triA (a 0) (a 2) (b 2), psl3f201_triB (a 0) (b 0) (b 2), psl3f201_triB (a 0) (b 1) (b 2), psl3f201_triA (a 1) (b 0) (b 1), psl3f201_triA (a 1) (b 0) (b 2), psl3f201_triA (a 1) (b 1) (b 2), psl3f201_triC (a 2) (b 0) (b 1), p10, p11, abs_nonneg (a 0 - b 2), abs_nonneg (a 2 - b 0), abs_nonneg (a 1 - b 1)]

theorem psl3f201_ps3_case_201_021_102 (a b : Fin 3 → ℝ)
    (h : is_line_distance_preference_profile a b ![psl3f201_PS3P201, psl3f201_PS3P021, psl3f201_PS3P102]) (σ : Equiv.Perm (Fin 3)) :
    probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P021, psl3f201_PS3P102] ≤ 3 * ∑ i, |a i - b (σ i)| := by
  have hX : ((psl3f201_psPhaseQ 3 ![psl3f201_PS3P201, psl3f201_PS3P021, psl3f201_PS3P102])^[3] (fun _ => 1, fun _ _ => 0)).2 = ![![(0 : ℚ), (0 : ℚ), (1 : ℚ)], ![(1 : ℚ), (0 : ℚ), (0 : ℚ)], ![(0 : ℚ), (1 : ℚ), (0 : ℚ)]] := by decide +kernel
  have e : probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P021, psl3f201_PS3P102] = (1/1 : ℝ) * |a 0 - b 2| + (1/1 : ℝ) * |a 1 - b 0| + (1/1 : ℝ) * |a 2 - b 1| := by
    unfold probabilistic_serial_line_cost
    simp only [psl3f201_psQ_cast, hX, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    push_cast; ring
  have p00 : |a 0 - b 2| ≤ |a 0 - b 0| := h 0 0 1 (by decide)
  have p01 : |a 0 - b 0| ≤ |a 0 - b 1| := h 0 1 2 (by decide)
  have p10 : |a 1 - b 0| ≤ |a 1 - b 2| := h 1 0 1 (by decide)
  have p11 : |a 1 - b 2| ≤ |a 1 - b 1| := h 1 1 2 (by decide)
  have p20 : |a 2 - b 1| ≤ |a 2 - b 0| := h 2 0 1 (by decide)
  have p21 : |a 2 - b 0| ≤ |a 2 - b 2| := h 2 1 2 (by decide)
  rw [e]
  rcases psl3f201_ps3_perm_cases σ with rfl | rfl | rfl | rfl | rfl | rfl
  · have hc : ∑ i, |a i - b (psl3f201_PS3P012 i)| = |a 0 - b 0| + |a 1 - b 1| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [p00, p10, p11, p20, p21, abs_nonneg (a 0 - b 0), abs_nonneg (a 1 - b 1), abs_nonneg (a 2 - b 2)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P021 i)| = |a 0 - b 0| + |a 1 - b 2| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [p00, p10, abs_nonneg (a 0 - b 0), abs_nonneg (a 1 - b 2), abs_nonneg (a 2 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P102 i)| = |a 0 - b 1| + |a 1 - b 0| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [p00, p01, p20, p21, abs_nonneg (a 0 - b 1), abs_nonneg (a 1 - b 0), abs_nonneg (a 2 - b 2)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P120 i)| = |a 0 - b 1| + |a 1 - b 2| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [p00, p01, p10, p20, abs_nonneg (a 0 - b 1), abs_nonneg (a 1 - b 2), abs_nonneg (a 2 - b 0)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P201 i)| = |a 0 - b 2| + |a 1 - b 0| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [abs_nonneg (a 0 - b 2), abs_nonneg (a 1 - b 0), abs_nonneg (a 2 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P210 i)| = |a 0 - b 2| + |a 1 - b 1| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [p10, p11, p20, abs_nonneg (a 0 - b 2), abs_nonneg (a 1 - b 1), abs_nonneg (a 2 - b 0)]

theorem psl3f201_ps3_case_201_021_120 (a b : Fin 3 → ℝ)
    (h : is_line_distance_preference_profile a b ![psl3f201_PS3P201, psl3f201_PS3P021, psl3f201_PS3P120]) (σ : Equiv.Perm (Fin 3)) :
    probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P021, psl3f201_PS3P120] ≤ 3 * ∑ i, |a i - b (σ i)| := by
  have hX : ((psl3f201_psPhaseQ 3 ![psl3f201_PS3P201, psl3f201_PS3P021, psl3f201_PS3P120])^[3] (fun _ => 1, fun _ _ => 0)).2 = ![![(0 : ℚ), (0 : ℚ), (1 : ℚ)], ![(1 : ℚ), (0 : ℚ), (0 : ℚ)], ![(0 : ℚ), (1 : ℚ), (0 : ℚ)]] := by decide +kernel
  have e : probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P021, psl3f201_PS3P120] = (1/1 : ℝ) * |a 0 - b 2| + (1/1 : ℝ) * |a 1 - b 0| + (1/1 : ℝ) * |a 2 - b 1| := by
    unfold probabilistic_serial_line_cost
    simp only [psl3f201_psQ_cast, hX, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    push_cast; ring
  have p00 : |a 0 - b 2| ≤ |a 0 - b 0| := h 0 0 1 (by decide)
  have p01 : |a 0 - b 0| ≤ |a 0 - b 1| := h 0 1 2 (by decide)
  have p10 : |a 1 - b 0| ≤ |a 1 - b 2| := h 1 0 1 (by decide)
  have p11 : |a 1 - b 2| ≤ |a 1 - b 1| := h 1 1 2 (by decide)
  have p20 : |a 2 - b 1| ≤ |a 2 - b 2| := h 2 0 1 (by decide)
  have p21 : |a 2 - b 2| ≤ |a 2 - b 0| := h 2 1 2 (by decide)
  rw [e]
  rcases psl3f201_ps3_perm_cases σ with rfl | rfl | rfl | rfl | rfl | rfl
  · have hc : ∑ i, |a i - b (psl3f201_PS3P012 i)| = |a 0 - b 0| + |a 1 - b 1| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [p00, p10, p11, p20, abs_nonneg (a 0 - b 0), abs_nonneg (a 1 - b 1), abs_nonneg (a 2 - b 2)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P021 i)| = |a 0 - b 0| + |a 1 - b 2| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [p00, p10, abs_nonneg (a 0 - b 0), abs_nonneg (a 1 - b 2), abs_nonneg (a 2 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P102 i)| = |a 0 - b 1| + |a 1 - b 0| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [p00, p01, p20, abs_nonneg (a 0 - b 1), abs_nonneg (a 1 - b 0), abs_nonneg (a 2 - b 2)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P120 i)| = |a 0 - b 1| + |a 1 - b 2| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [p00, p01, p10, p20, p21, abs_nonneg (a 0 - b 1), abs_nonneg (a 1 - b 2), abs_nonneg (a 2 - b 0)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P201 i)| = |a 0 - b 2| + |a 1 - b 0| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [abs_nonneg (a 0 - b 2), abs_nonneg (a 1 - b 0), abs_nonneg (a 2 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P210 i)| = |a 0 - b 2| + |a 1 - b 1| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [p10, p11, p20, p21, abs_nonneg (a 0 - b 2), abs_nonneg (a 1 - b 1), abs_nonneg (a 2 - b 0)]

theorem psl3f201_ps3_case_201_021_201 (a b : Fin 3 → ℝ)
    (h : is_line_distance_preference_profile a b ![psl3f201_PS3P201, psl3f201_PS3P021, psl3f201_PS3P201]) (σ : Equiv.Perm (Fin 3)) :
    probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P021, psl3f201_PS3P201] ≤ 3 * ∑ i, |a i - b (σ i)| := by
  have hX : ((psl3f201_psPhaseQ 3 ![psl3f201_PS3P201, psl3f201_PS3P021, psl3f201_PS3P201])^[3] (fun _ => 1, fun _ _ => 0)).2 = ![![(1/6 : ℚ), (1/3 : ℚ), (1/2 : ℚ)], ![(2/3 : ℚ), (1/3 : ℚ), (0 : ℚ)], ![(1/6 : ℚ), (1/3 : ℚ), (1/2 : ℚ)]] := by decide +kernel
  have e : probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P021, psl3f201_PS3P201] = (1/6 : ℝ) * |a 0 - b 0| + (1/3 : ℝ) * |a 0 - b 1| + (1/2 : ℝ) * |a 0 - b 2| + (2/3 : ℝ) * |a 1 - b 0| + (1/3 : ℝ) * |a 1 - b 1| + (1/6 : ℝ) * |a 2 - b 0| + (1/3 : ℝ) * |a 2 - b 1| + (1/2 : ℝ) * |a 2 - b 2| := by
    unfold probabilistic_serial_line_cost
    simp only [psl3f201_psQ_cast, hX, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    push_cast; ring
  have p00 : |a 0 - b 2| ≤ |a 0 - b 0| := h 0 0 1 (by decide)
  have p01 : |a 0 - b 0| ≤ |a 0 - b 1| := h 0 1 2 (by decide)
  have p10 : |a 1 - b 0| ≤ |a 1 - b 2| := h 1 0 1 (by decide)
  have p11 : |a 1 - b 2| ≤ |a 1 - b 1| := h 1 1 2 (by decide)
  have p20 : |a 2 - b 2| ≤ |a 2 - b 0| := h 2 0 1 (by decide)
  have p21 : |a 2 - b 0| ≤ |a 2 - b 1| := h 2 1 2 (by decide)
  rw [e]
  rcases psl3f201_ps3_perm_cases σ with rfl | rfl | rfl | rfl | rfl | rfl
  · have hc : ∑ i, |a i - b (psl3f201_PS3P012 i)| = |a 0 - b 0| + |a 1 - b 1| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triA (a 0) (b 0) (b 2), psl3f201_triB (a 0) (b 1) (b 2), psl3f201_triA (a 0) (b 1) (b 2), psl3f201_triA (a 1) (b 1) (b 2), psl3f201_triB (a 2) (b 0) (b 2), psl3f201_triB (a 2) (b 1) (b 2), p00, p10, p11, abs_nonneg (a 2 - b 2), abs_nonneg (a 0 - b 0), abs_nonneg (a 1 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P021 i)| = |a 0 - b 0| + |a 1 - b 2| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triB (a 0) (a 1) (b 0), psl3f201_triA (a 0) (a 1) (b 0), psl3f201_triC (a 0) (b 0) (b 1), psl3f201_triB (a 1) (a 2) (b 0), psl3f201_triC (a 1) (a 2) (b 1), psl3f201_triA (a 2) (b 0) (b 1), p00, p10, p20, p21, abs_nonneg (a 1 - b 2), abs_nonneg (a 0 - b 0), abs_nonneg (a 2 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P102 i)| = |a 0 - b 1| + |a 1 - b 0| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triA (a 0) (a 2) (b 1), psl3f201_triB (a 0) (a 2) (b 2), psl3f201_triA (a 0) (b 0) (b 1), psl3f201_triA (a 1) (a 2) (b 0), psl3f201_triB (a 1) (a 2) (b 2), psl3f201_triC (a 1) (b 0) (b 1), p00, p01, p11, abs_nonneg (a 1 - b 0), abs_nonneg (a 2 - b 2), abs_nonneg (a 0 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P120 i)| = |a 0 - b 1| + |a 1 - b 2| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triA (a 0) (b 0) (b 1), psl3f201_triB (a 1) (a 2) (b 0), psl3f201_triA (a 1) (a 2) (b 2), psl3f201_triA (a 1) (b 0) (b 2), psl3f201_triB (a 1) (b 1) (b 2), psl3f201_triC (a 2) (b 0) (b 1), psl3f201_triA (b 0) (b 1) (b 2), p00, p01, p10, p20, abs_nonneg (a 2 - b 0), abs_nonneg (a 0 - b 1), abs_nonneg (a 1 - b 2)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P201 i)| = |a 0 - b 2| + |a 1 - b 0| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triC (a 0) (a 1) (b 0), psl3f201_triB (a 0) (a 1) (b 2), psl3f201_triB (a 0) (b 1) (b 2), psl3f201_triB (a 1) (a 2) (b 0), psl3f201_triA (a 1) (a 2) (b 0), psl3f201_triC (a 1) (a 2) (b 1), psl3f201_triA (a 2) (b 1) (b 2), p11, p20, p21, abs_nonneg (a 0 - b 2), abs_nonneg (a 1 - b 0), abs_nonneg (a 2 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P210 i)| = |a 0 - b 2| + |a 1 - b 1| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triC (a 0) (a 1) (b 1), psl3f201_triB (a 0) (a 1) (b 2), psl3f201_triC (a 0) (a 2) (b 0), psl3f201_triB (a 0) (a 2) (b 2), psl3f201_triC (a 1) (a 2) (b 0), psl3f201_triB (a 1) (a 2) (b 0), psl3f201_triA (a 1) (a 2) (b 1), p10, p11, p20, abs_nonneg (a 0 - b 2), abs_nonneg (a 1 - b 1), abs_nonneg (a 2 - b 0)]

theorem psl3f201_ps3_case_201_021_210 (a b : Fin 3 → ℝ)
    (h : is_line_distance_preference_profile a b ![psl3f201_PS3P201, psl3f201_PS3P021, psl3f201_PS3P210]) (σ : Equiv.Perm (Fin 3)) :
    probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P021, psl3f201_PS3P210] ≤ 3 * ∑ i, |a i - b (σ i)| := by
  have hX : ((psl3f201_psPhaseQ 3 ![psl3f201_PS3P201, psl3f201_PS3P021, psl3f201_PS3P210])^[3] (fun _ => 1, fun _ _ => 0)).2 = ![![(1/4 : ℚ), (1/4 : ℚ), (1/2 : ℚ)], ![(3/4 : ℚ), (1/4 : ℚ), (0 : ℚ)], ![(0 : ℚ), (1/2 : ℚ), (1/2 : ℚ)]] := by decide +kernel
  have e : probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P021, psl3f201_PS3P210] = (1/4 : ℝ) * |a 0 - b 0| + (1/4 : ℝ) * |a 0 - b 1| + (1/2 : ℝ) * |a 0 - b 2| + (3/4 : ℝ) * |a 1 - b 0| + (1/4 : ℝ) * |a 1 - b 1| + (1/2 : ℝ) * |a 2 - b 1| + (1/2 : ℝ) * |a 2 - b 2| := by
    unfold probabilistic_serial_line_cost
    simp only [psl3f201_psQ_cast, hX, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    push_cast; ring
  have p00 : |a 0 - b 2| ≤ |a 0 - b 0| := h 0 0 1 (by decide)
  have p01 : |a 0 - b 0| ≤ |a 0 - b 1| := h 0 1 2 (by decide)
  have p10 : |a 1 - b 0| ≤ |a 1 - b 2| := h 1 0 1 (by decide)
  have p11 : |a 1 - b 2| ≤ |a 1 - b 1| := h 1 1 2 (by decide)
  have p20 : |a 2 - b 2| ≤ |a 2 - b 1| := h 2 0 1 (by decide)
  have p21 : |a 2 - b 1| ≤ |a 2 - b 0| := h 2 1 2 (by decide)
  rw [e]
  rcases psl3f201_ps3_perm_cases σ with rfl | rfl | rfl | rfl | rfl | rfl
  · have hc : ∑ i, |a i - b (psl3f201_PS3P012 i)| = |a 0 - b 0| + |a 1 - b 1| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triC (a 0) (a 1) (b 1), psl3f201_triB (a 0) (a 1) (b 2), psl3f201_triA (a 0) (b 0) (b 2), psl3f201_triA (a 1) (b 1) (b 2), psl3f201_triB (a 2) (b 0) (b 2), psl3f201_triB (a 2) (b 1) (b 2), p00, p10, p11, p21, abs_nonneg (a 2 - b 2), abs_nonneg (a 0 - b 0), abs_nonneg (a 1 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P021 i)| = |a 0 - b 0| + |a 1 - b 2| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triC (a 0) (b 0) (b 1), psl3f201_triA (a 1) (b 0) (b 2), psl3f201_triB (a 1) (b 1) (b 2), psl3f201_triA (a 2) (b 0) (b 1), psl3f201_triB (a 2) (b 0) (b 2), psl3f201_triA (a 2) (b 1) (b 2), p00, p10, p20, abs_nonneg (a 0 - b 2), abs_nonneg (a 1 - b 2), abs_nonneg (a 0 - b 0), abs_nonneg (a 2 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P102 i)| = |a 0 - b 1| + |a 1 - b 0| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triB (a 0) (a 1) (b 0), psl3f201_triA (a 0) (a 1) (b 1), psl3f201_triA (a 0) (b 1) (b 2), psl3f201_triB (a 2) (b 1) (b 2), p00, p01, abs_nonneg (a 1 - b 0), abs_nonneg (a 2 - b 2), abs_nonneg (a 0 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P120 i)| = |a 0 - b 1| + |a 1 - b 2| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triB (a 0) (a 1) (b 0), psl3f201_triA (a 0) (a 1) (b 1), psl3f201_triB (a 1) (a 2) (b 0), psl3f201_triA (a 1) (a 2) (b 2), psl3f201_triB (a 1) (b 1) (b 2), psl3f201_triA (a 2) (b 1) (b 2), p00, p01, p10, p20, p21, abs_nonneg (a 0 - b 1), abs_nonneg (a 1 - b 2), abs_nonneg (a 2 - b 0)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P201 i)| = |a 0 - b 2| + |a 1 - b 0| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triA (a 0) (b 0) (b 2), psl3f201_triB (a 0) (b 1) (b 2), psl3f201_triC (a 1) (b 0) (b 1), psl3f201_triA (a 2) (b 0) (b 1), psl3f201_triB (a 2) (b 0) (b 2), psl3f201_triA (a 2) (b 1) (b 2), p01, p20, abs_nonneg (a 0 - b 2), abs_nonneg (a 1 - b 0), abs_nonneg (a 2 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P210 i)| = |a 0 - b 2| + |a 1 - b 1| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triC (a 0) (a 1) (b 1), psl3f201_triB (a 0) (a 1) (b 2), psl3f201_triB (a 0) (b 0) (b 2), psl3f201_triA (a 2) (b 0) (b 2), p10, p11, p20, p21, abs_nonneg (a 0 - b 2), abs_nonneg (a 1 - b 1), abs_nonneg (a 2 - b 0)]

theorem psl3f201_ps3_case_201_102_012 (a b : Fin 3 → ℝ)
    (h : is_line_distance_preference_profile a b ![psl3f201_PS3P201, psl3f201_PS3P102, psl3f201_PS3P012]) (σ : Equiv.Perm (Fin 3)) :
    probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P102, psl3f201_PS3P012] ≤ 3 * ∑ i, |a i - b (σ i)| := by
  have hX : ((psl3f201_psPhaseQ 3 ![psl3f201_PS3P201, psl3f201_PS3P102, psl3f201_PS3P012])^[3] (fun _ => 1, fun _ _ => 0)).2 = ![![(0 : ℚ), (0 : ℚ), (1 : ℚ)], ![(0 : ℚ), (1 : ℚ), (0 : ℚ)], ![(1 : ℚ), (0 : ℚ), (0 : ℚ)]] := by decide +kernel
  have e : probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P102, psl3f201_PS3P012] = (1/1 : ℝ) * |a 0 - b 2| + (1/1 : ℝ) * |a 1 - b 1| + (1/1 : ℝ) * |a 2 - b 0| := by
    unfold probabilistic_serial_line_cost
    simp only [psl3f201_psQ_cast, hX, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    push_cast; ring
  have p00 : |a 0 - b 2| ≤ |a 0 - b 0| := h 0 0 1 (by decide)
  have p01 : |a 0 - b 0| ≤ |a 0 - b 1| := h 0 1 2 (by decide)
  have p10 : |a 1 - b 1| ≤ |a 1 - b 0| := h 1 0 1 (by decide)
  have p11 : |a 1 - b 0| ≤ |a 1 - b 2| := h 1 1 2 (by decide)
  have p20 : |a 2 - b 0| ≤ |a 2 - b 1| := h 2 0 1 (by decide)
  have p21 : |a 2 - b 1| ≤ |a 2 - b 2| := h 2 1 2 (by decide)
  rw [e]
  rcases psl3f201_ps3_perm_cases σ with rfl | rfl | rfl | rfl | rfl | rfl
  · have hc : ∑ i, |a i - b (psl3f201_PS3P012 i)| = |a 0 - b 0| + |a 1 - b 1| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [p00, p20, p21, abs_nonneg (a 0 - b 0), abs_nonneg (a 1 - b 1), abs_nonneg (a 2 - b 2)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P021 i)| = |a 0 - b 0| + |a 1 - b 2| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [p00, p10, p11, p20, abs_nonneg (a 0 - b 0), abs_nonneg (a 1 - b 2), abs_nonneg (a 2 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P102 i)| = |a 0 - b 1| + |a 1 - b 0| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [p00, p01, p10, p20, p21, abs_nonneg (a 0 - b 1), abs_nonneg (a 1 - b 0), abs_nonneg (a 2 - b 2)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P120 i)| = |a 0 - b 1| + |a 1 - b 2| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [p00, p01, p10, p11, abs_nonneg (a 0 - b 1), abs_nonneg (a 1 - b 2), abs_nonneg (a 2 - b 0)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P201 i)| = |a 0 - b 2| + |a 1 - b 0| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [p10, p20, abs_nonneg (a 0 - b 2), abs_nonneg (a 1 - b 0), abs_nonneg (a 2 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P210 i)| = |a 0 - b 2| + |a 1 - b 1| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [abs_nonneg (a 0 - b 2), abs_nonneg (a 1 - b 1), abs_nonneg (a 2 - b 0)]

theorem psl3f201_ps3_case_201_102_021 (a b : Fin 3 → ℝ)
    (h : is_line_distance_preference_profile a b ![psl3f201_PS3P201, psl3f201_PS3P102, psl3f201_PS3P021]) (σ : Equiv.Perm (Fin 3)) :
    probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P102, psl3f201_PS3P021] ≤ 3 * ∑ i, |a i - b (σ i)| := by
  have hX : ((psl3f201_psPhaseQ 3 ![psl3f201_PS3P201, psl3f201_PS3P102, psl3f201_PS3P021])^[3] (fun _ => 1, fun _ _ => 0)).2 = ![![(0 : ℚ), (0 : ℚ), (1 : ℚ)], ![(0 : ℚ), (1 : ℚ), (0 : ℚ)], ![(1 : ℚ), (0 : ℚ), (0 : ℚ)]] := by decide +kernel
  have e : probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P102, psl3f201_PS3P021] = (1/1 : ℝ) * |a 0 - b 2| + (1/1 : ℝ) * |a 1 - b 1| + (1/1 : ℝ) * |a 2 - b 0| := by
    unfold probabilistic_serial_line_cost
    simp only [psl3f201_psQ_cast, hX, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    push_cast; ring
  have p00 : |a 0 - b 2| ≤ |a 0 - b 0| := h 0 0 1 (by decide)
  have p01 : |a 0 - b 0| ≤ |a 0 - b 1| := h 0 1 2 (by decide)
  have p10 : |a 1 - b 1| ≤ |a 1 - b 0| := h 1 0 1 (by decide)
  have p11 : |a 1 - b 0| ≤ |a 1 - b 2| := h 1 1 2 (by decide)
  have p20 : |a 2 - b 0| ≤ |a 2 - b 2| := h 2 0 1 (by decide)
  have p21 : |a 2 - b 2| ≤ |a 2 - b 1| := h 2 1 2 (by decide)
  rw [e]
  rcases psl3f201_ps3_perm_cases σ with rfl | rfl | rfl | rfl | rfl | rfl
  · have hc : ∑ i, |a i - b (psl3f201_PS3P012 i)| = |a 0 - b 0| + |a 1 - b 1| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [p00, p20, abs_nonneg (a 0 - b 0), abs_nonneg (a 1 - b 1), abs_nonneg (a 2 - b 2)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P021 i)| = |a 0 - b 0| + |a 1 - b 2| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [p00, p10, p11, p20, p21, abs_nonneg (a 0 - b 0), abs_nonneg (a 1 - b 2), abs_nonneg (a 2 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P102 i)| = |a 0 - b 1| + |a 1 - b 0| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [p00, p01, p10, p20, abs_nonneg (a 0 - b 1), abs_nonneg (a 1 - b 0), abs_nonneg (a 2 - b 2)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P120 i)| = |a 0 - b 1| + |a 1 - b 2| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [p00, p01, p10, p11, abs_nonneg (a 0 - b 1), abs_nonneg (a 1 - b 2), abs_nonneg (a 2 - b 0)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P201 i)| = |a 0 - b 2| + |a 1 - b 0| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [p10, p20, p21, abs_nonneg (a 0 - b 2), abs_nonneg (a 1 - b 0), abs_nonneg (a 2 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P210 i)| = |a 0 - b 2| + |a 1 - b 1| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [abs_nonneg (a 0 - b 2), abs_nonneg (a 1 - b 1), abs_nonneg (a 2 - b 0)]

theorem psl3f201_ps3_case_201_102_102 (a b : Fin 3 → ℝ)
    (h : is_line_distance_preference_profile a b ![psl3f201_PS3P201, psl3f201_PS3P102, psl3f201_PS3P102]) (σ : Equiv.Perm (Fin 3)) :
    probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P102, psl3f201_PS3P102] ≤ 3 * ∑ i, |a i - b (σ i)| := by
  have hX : ((psl3f201_psPhaseQ 3 ![psl3f201_PS3P201, psl3f201_PS3P102, psl3f201_PS3P102])^[3] (fun _ => 1, fun _ _ => 0)).2 = ![![(0 : ℚ), (0 : ℚ), (1 : ℚ)], ![(1/2 : ℚ), (1/2 : ℚ), (0 : ℚ)], ![(1/2 : ℚ), (1/2 : ℚ), (0 : ℚ)]] := by decide +kernel
  have e : probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P102, psl3f201_PS3P102] = (1/1 : ℝ) * |a 0 - b 2| + (1/2 : ℝ) * |a 1 - b 0| + (1/2 : ℝ) * |a 1 - b 1| + (1/2 : ℝ) * |a 2 - b 0| + (1/2 : ℝ) * |a 2 - b 1| := by
    unfold probabilistic_serial_line_cost
    simp only [psl3f201_psQ_cast, hX, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    push_cast; ring
  have p00 : |a 0 - b 2| ≤ |a 0 - b 0| := h 0 0 1 (by decide)
  have p01 : |a 0 - b 0| ≤ |a 0 - b 1| := h 0 1 2 (by decide)
  have p10 : |a 1 - b 1| ≤ |a 1 - b 0| := h 1 0 1 (by decide)
  have p11 : |a 1 - b 0| ≤ |a 1 - b 2| := h 1 1 2 (by decide)
  have p20 : |a 2 - b 1| ≤ |a 2 - b 0| := h 2 0 1 (by decide)
  have p21 : |a 2 - b 0| ≤ |a 2 - b 2| := h 2 1 2 (by decide)
  rw [e]
  rcases psl3f201_ps3_perm_cases σ with rfl | rfl | rfl | rfl | rfl | rfl
  · have hc : ∑ i, |a i - b (psl3f201_PS3P012 i)| = |a 0 - b 0| + |a 1 - b 1| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triB (a 1) (a 2) (b 1), psl3f201_triC (a 1) (a 2) (b 2), psl3f201_triC (a 1) (b 1) (b 2), psl3f201_triA (a 1) (b 1) (b 2), p00, p11, p20, p21, abs_nonneg (a 0 - b 0), abs_nonneg (a 1 - b 1), abs_nonneg (a 2 - b 2)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P021 i)| = |a 0 - b 0| + |a 1 - b 2| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triB (a 1) (a 2) (b 1), psl3f201_triA (a 1) (a 2) (b 2), p00, p10, p11, p21, abs_nonneg (a 0 - b 0), abs_nonneg (a 2 - b 1), abs_nonneg (a 1 - b 2)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P102 i)| = |a 0 - b 1| + |a 1 - b 0| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [p00, p01, p10, p20, p21, abs_nonneg (a 0 - b 1), abs_nonneg (a 1 - b 0), abs_nonneg (a 2 - b 2)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P120 i)| = |a 0 - b 1| + |a 1 - b 2| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [p00, p01, p10, p11, p20, abs_nonneg (a 0 - b 1), abs_nonneg (a 1 - b 2), abs_nonneg (a 2 - b 0)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P201 i)| = |a 0 - b 2| + |a 1 - b 0| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triA (a 1) (a 2) (b 0), psl3f201_triB (a 1) (a 2) (b 1), p10, abs_nonneg (a 0 - b 2), abs_nonneg (a 2 - b 1), abs_nonneg (a 1 - b 0)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P210 i)| = |a 0 - b 2| + |a 1 - b 1| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triC (a 1) (a 2) (b 0), psl3f201_triB (a 1) (a 2) (b 1), p20, abs_nonneg (a 0 - b 2), abs_nonneg (a 1 - b 1), abs_nonneg (a 2 - b 0)]

theorem psl3f201_ps3_case_201_102_120 (a b : Fin 3 → ℝ)
    (h : is_line_distance_preference_profile a b ![psl3f201_PS3P201, psl3f201_PS3P102, psl3f201_PS3P120]) (σ : Equiv.Perm (Fin 3)) :
    probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P102, psl3f201_PS3P120] ≤ 3 * ∑ i, |a i - b (σ i)| := by
  have hX : ((psl3f201_psPhaseQ 3 ![psl3f201_PS3P201, psl3f201_PS3P102, psl3f201_PS3P120])^[3] (fun _ => 1, fun _ _ => 0)).2 = ![![(1/4 : ℚ), (0 : ℚ), (3/4 : ℚ)], ![(1/2 : ℚ), (1/2 : ℚ), (0 : ℚ)], ![(1/4 : ℚ), (1/2 : ℚ), (1/4 : ℚ)]] := by decide +kernel
  have e : probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P102, psl3f201_PS3P120] = (1/4 : ℝ) * |a 0 - b 0| + (3/4 : ℝ) * |a 0 - b 2| + (1/2 : ℝ) * |a 1 - b 0| + (1/2 : ℝ) * |a 1 - b 1| + (1/4 : ℝ) * |a 2 - b 0| + (1/2 : ℝ) * |a 2 - b 1| + (1/4 : ℝ) * |a 2 - b 2| := by
    unfold probabilistic_serial_line_cost
    simp only [psl3f201_psQ_cast, hX, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    push_cast; ring
  have p00 : |a 0 - b 2| ≤ |a 0 - b 0| := h 0 0 1 (by decide)
  have p01 : |a 0 - b 0| ≤ |a 0 - b 1| := h 0 1 2 (by decide)
  have p10 : |a 1 - b 1| ≤ |a 1 - b 0| := h 1 0 1 (by decide)
  have p11 : |a 1 - b 0| ≤ |a 1 - b 2| := h 1 1 2 (by decide)
  have p20 : |a 2 - b 1| ≤ |a 2 - b 2| := h 2 0 1 (by decide)
  have p21 : |a 2 - b 2| ≤ |a 2 - b 0| := h 2 1 2 (by decide)
  rw [e]
  rcases psl3f201_ps3_perm_cases σ with rfl | rfl | rfl | rfl | rfl | rfl
  · have hc : ∑ i, |a i - b (psl3f201_PS3P012 i)| = |a 0 - b 0| + |a 1 - b 1| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triA (a 0) (a 2) (b 0), psl3f201_triB (a 0) (a 2) (b 2), psl3f201_triB (a 1) (a 2) (b 1), psl3f201_triC (a 1) (a 2) (b 2), psl3f201_triB (a 1) (b 0) (b 1), psl3f201_triA (a 2) (b 0) (b 1), p00, p11, p20, abs_nonneg (a 1 - b 1), abs_nonneg (a 0 - b 0), abs_nonneg (a 2 - b 2)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P021 i)| = |a 0 - b 0| + |a 1 - b 2| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triC (a 0) (a 1) (b 1), psl3f201_triB (a 0) (a 1) (b 2), psl3f201_triA (a 0) (b 0) (b 1), psl3f201_triC (a 0) (b 0) (b 2), psl3f201_triA (a 0) (b 0) (b 2), psl3f201_triB (a 1) (a 2) (b 1), psl3f201_triA (a 1) (a 2) (b 2), psl3f201_triB (a 2) (b 0) (b 1), p00, p10, p11, abs_nonneg (a 2 - b 1), abs_nonneg (a 0 - b 0), abs_nonneg (a 1 - b 2)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P102 i)| = |a 0 - b 1| + |a 1 - b 0| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triA (a 0) (b 0) (b 1), psl3f201_triA (a 1) (b 0) (b 1), psl3f201_triB (a 2) (b 0) (b 1), p00, p01, p10, p20, abs_nonneg (a 2 - b 2), abs_nonneg (a 0 - b 1), abs_nonneg (a 1 - b 0)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P120 i)| = |a 0 - b 1| + |a 1 - b 2| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [p00, p01, p10, p11, p20, p21, abs_nonneg (a 0 - b 1), abs_nonneg (a 1 - b 2), abs_nonneg (a 2 - b 0)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P201 i)| = |a 0 - b 2| + |a 1 - b 0| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triB (a 0) (b 1) (b 2), psl3f201_triA (a 1) (b 0) (b 1), psl3f201_triB (a 2) (b 0) (b 1), psl3f201_triA (a 2) (b 1) (b 2), p01, p10, p21, abs_nonneg (a 0 - b 2), abs_nonneg (a 2 - b 1), abs_nonneg (a 1 - b 0)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P210 i)| = |a 0 - b 2| + |a 1 - b 1| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triB (a 0) (b 0) (b 2), psl3f201_triB (a 1) (b 0) (b 1), psl3f201_triA (a 2) (b 0) (b 1), psl3f201_triA (a 2) (b 0) (b 2), p20, p21, abs_nonneg (a 0 - b 2), abs_nonneg (a 1 - b 1), abs_nonneg (a 2 - b 0)]

theorem psl3f201_ps3_case_201_102_201 (a b : Fin 3 → ℝ)
    (h : is_line_distance_preference_profile a b ![psl3f201_PS3P201, psl3f201_PS3P102, psl3f201_PS3P201]) (σ : Equiv.Perm (Fin 3)) :
    probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P102, psl3f201_PS3P201] ≤ 3 * ∑ i, |a i - b (σ i)| := by
  have hX : ((psl3f201_psPhaseQ 3 ![psl3f201_PS3P201, psl3f201_PS3P102, psl3f201_PS3P201])^[3] (fun _ => 1, fun _ _ => 0)).2 = ![![(1/2 : ℚ), (0 : ℚ), (1/2 : ℚ)], ![(0 : ℚ), (1 : ℚ), (0 : ℚ)], ![(1/2 : ℚ), (0 : ℚ), (1/2 : ℚ)]] := by decide +kernel
  have e : probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P102, psl3f201_PS3P201] = (1/2 : ℝ) * |a 0 - b 0| + (1/2 : ℝ) * |a 0 - b 2| + (1/1 : ℝ) * |a 1 - b 1| + (1/2 : ℝ) * |a 2 - b 0| + (1/2 : ℝ) * |a 2 - b 2| := by
    unfold probabilistic_serial_line_cost
    simp only [psl3f201_psQ_cast, hX, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    push_cast; ring
  have p00 : |a 0 - b 2| ≤ |a 0 - b 0| := h 0 0 1 (by decide)
  have p01 : |a 0 - b 0| ≤ |a 0 - b 1| := h 0 1 2 (by decide)
  have p10 : |a 1 - b 1| ≤ |a 1 - b 0| := h 1 0 1 (by decide)
  have p11 : |a 1 - b 0| ≤ |a 1 - b 2| := h 1 1 2 (by decide)
  have p20 : |a 2 - b 2| ≤ |a 2 - b 0| := h 2 0 1 (by decide)
  have p21 : |a 2 - b 0| ≤ |a 2 - b 1| := h 2 1 2 (by decide)
  rw [e]
  rcases psl3f201_ps3_perm_cases σ with rfl | rfl | rfl | rfl | rfl | rfl
  · have hc : ∑ i, |a i - b (psl3f201_PS3P012 i)| = |a 0 - b 0| + |a 1 - b 1| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triA (a 0) (b 0) (b 2), psl3f201_triB (a 2) (b 0) (b 2), p00, abs_nonneg (a 1 - b 1), abs_nonneg (a 2 - b 2), abs_nonneg (a 0 - b 0)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P021 i)| = |a 0 - b 0| + |a 1 - b 2| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [p00, p10, p11, p20, p21, abs_nonneg (a 0 - b 0), abs_nonneg (a 1 - b 2), abs_nonneg (a 2 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P102 i)| = |a 0 - b 1| + |a 1 - b 0| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triA (a 0) (a 2) (b 0), psl3f201_triB (a 0) (a 2) (b 2), p00, p01, p10, abs_nonneg (a 1 - b 0), abs_nonneg (a 2 - b 2), abs_nonneg (a 0 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P120 i)| = |a 0 - b 1| + |a 1 - b 2| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [p00, p01, p10, p11, p20, abs_nonneg (a 0 - b 1), abs_nonneg (a 1 - b 2), abs_nonneg (a 2 - b 0)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P201 i)| = |a 0 - b 2| + |a 1 - b 0| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triB (a 0) (b 0) (b 2), psl3f201_triB (a 0) (b 1) (b 2), psl3f201_triA (a 0) (b 1) (b 2), psl3f201_triA (a 1) (a 2) (b 0), psl3f201_triB (a 1) (a 2) (b 1), psl3f201_triA (a 2) (b 0) (b 2), p10, p20, p21, abs_nonneg (a 0 - b 2), abs_nonneg (a 1 - b 0), abs_nonneg (a 2 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P210 i)| = |a 0 - b 2| + |a 1 - b 1| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triC (a 0) (a 2) (b 0), psl3f201_triB (a 0) (a 2) (b 2), p20, abs_nonneg (a 0 - b 2), abs_nonneg (a 1 - b 1), abs_nonneg (a 2 - b 0)]

theorem psl3f201_ps3_case_201_102_210 (a b : Fin 3 → ℝ)
    (h : is_line_distance_preference_profile a b ![psl3f201_PS3P201, psl3f201_PS3P102, psl3f201_PS3P210]) (σ : Equiv.Perm (Fin 3)) :
    probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P102, psl3f201_PS3P210] ≤ 3 * ∑ i, |a i - b (σ i)| := by
  have hX : ((psl3f201_psPhaseQ 3 ![psl3f201_PS3P201, psl3f201_PS3P102, psl3f201_PS3P210])^[3] (fun _ => 1, fun _ _ => 0)).2 = ![![(1/2 : ℚ), (0 : ℚ), (1/2 : ℚ)], ![(1/4 : ℚ), (3/4 : ℚ), (0 : ℚ)], ![(1/4 : ℚ), (1/4 : ℚ), (1/2 : ℚ)]] := by decide +kernel
  have e : probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P102, psl3f201_PS3P210] = (1/2 : ℝ) * |a 0 - b 0| + (1/2 : ℝ) * |a 0 - b 2| + (1/4 : ℝ) * |a 1 - b 0| + (3/4 : ℝ) * |a 1 - b 1| + (1/4 : ℝ) * |a 2 - b 0| + (1/4 : ℝ) * |a 2 - b 1| + (1/2 : ℝ) * |a 2 - b 2| := by
    unfold probabilistic_serial_line_cost
    simp only [psl3f201_psQ_cast, hX, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    push_cast; ring
  have p00 : |a 0 - b 2| ≤ |a 0 - b 0| := h 0 0 1 (by decide)
  have p01 : |a 0 - b 0| ≤ |a 0 - b 1| := h 0 1 2 (by decide)
  have p10 : |a 1 - b 1| ≤ |a 1 - b 0| := h 1 0 1 (by decide)
  have p11 : |a 1 - b 0| ≤ |a 1 - b 2| := h 1 1 2 (by decide)
  have p20 : |a 2 - b 2| ≤ |a 2 - b 1| := h 2 0 1 (by decide)
  have p21 : |a 2 - b 1| ≤ |a 2 - b 0| := h 2 1 2 (by decide)
  rw [e]
  rcases psl3f201_ps3_perm_cases σ with rfl | rfl | rfl | rfl | rfl | rfl
  · have hc : ∑ i, |a i - b (psl3f201_PS3P012 i)| = |a 0 - b 0| + |a 1 - b 1| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triA (a 0) (b 0) (b 2), psl3f201_triC (a 1) (b 1) (b 2), psl3f201_triB (a 2) (b 0) (b 2), psl3f201_triA (a 2) (b 1) (b 2), p00, p11, p21, abs_nonneg (a 1 - b 1), abs_nonneg (a 2 - b 2), abs_nonneg (a 0 - b 0)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P021 i)| = |a 0 - b 0| + |a 1 - b 2| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triA (a 0) (a 2) (b 0), psl3f201_triB (a 0) (a 2) (b 2), psl3f201_triA (a 1) (a 2) (b 0), psl3f201_triB (a 1) (a 2) (b 2), p00, p10, p11, p20, abs_nonneg (a 2 - b 1), abs_nonneg (a 0 - b 0), abs_nonneg (a 1 - b 2)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P102 i)| = |a 0 - b 1| + |a 1 - b 0| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triB (a 0) (a 1) (b 1), psl3f201_triA (a 0) (a 1) (b 2), psl3f201_triA (a 0) (a 2) (b 1), psl3f201_triB (a 0) (a 2) (b 2), psl3f201_triC (a 1) (a 2) (b 2), psl3f201_triB (a 1) (a 2) (b 2), psl3f201_triC (a 1) (b 0) (b 2), psl3f201_triA (a 1) (b 0) (b 2), psl3f201_triB (a 2) (b 0) (b 2), p00, p01, p10, abs_nonneg (a 0 - b 1), abs_nonneg (a 1 - b 0), abs_nonneg (a 2 - b 2)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P120 i)| = |a 0 - b 1| + |a 1 - b 2| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [p00, p01, p10, p11, p20, p21, abs_nonneg (a 0 - b 1), abs_nonneg (a 1 - b 2), abs_nonneg (a 2 - b 0)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P201 i)| = |a 0 - b 2| + |a 1 - b 0| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triB (a 0) (b 1) (b 2), psl3f201_triA (a 1) (a 2) (b 0), psl3f201_triB (a 1) (a 2) (b 1), psl3f201_triA (a 2) (b 1) (b 2), p01, p10, p20, abs_nonneg (a 0 - b 2), abs_nonneg (a 1 - b 0), abs_nonneg (a 2 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P210 i)| = |a 0 - b 2| + |a 1 - b 1| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triB (a 0) (b 0) (b 2), psl3f201_triB (a 1) (b 0) (b 1), psl3f201_triA (a 2) (b 0) (b 1), psl3f201_triA (a 2) (b 0) (b 2), p20, p21, abs_nonneg (a 0 - b 2), abs_nonneg (a 1 - b 1), abs_nonneg (a 2 - b 0)]

theorem psl3f201_ps3_case_201_120_012 (a b : Fin 3 → ℝ)
    (h : is_line_distance_preference_profile a b ![psl3f201_PS3P201, psl3f201_PS3P120, psl3f201_PS3P012]) (σ : Equiv.Perm (Fin 3)) :
    probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P120, psl3f201_PS3P012] ≤ 3 * ∑ i, |a i - b (σ i)| := by
  have hX : ((psl3f201_psPhaseQ 3 ![psl3f201_PS3P201, psl3f201_PS3P120, psl3f201_PS3P012])^[3] (fun _ => 1, fun _ _ => 0)).2 = ![![(0 : ℚ), (0 : ℚ), (1 : ℚ)], ![(0 : ℚ), (1 : ℚ), (0 : ℚ)], ![(1 : ℚ), (0 : ℚ), (0 : ℚ)]] := by decide +kernel
  have e : probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P120, psl3f201_PS3P012] = (1/1 : ℝ) * |a 0 - b 2| + (1/1 : ℝ) * |a 1 - b 1| + (1/1 : ℝ) * |a 2 - b 0| := by
    unfold probabilistic_serial_line_cost
    simp only [psl3f201_psQ_cast, hX, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    push_cast; ring
  have p00 : |a 0 - b 2| ≤ |a 0 - b 0| := h 0 0 1 (by decide)
  have p01 : |a 0 - b 0| ≤ |a 0 - b 1| := h 0 1 2 (by decide)
  have p10 : |a 1 - b 1| ≤ |a 1 - b 2| := h 1 0 1 (by decide)
  have p11 : |a 1 - b 2| ≤ |a 1 - b 0| := h 1 1 2 (by decide)
  have p20 : |a 2 - b 0| ≤ |a 2 - b 1| := h 2 0 1 (by decide)
  have p21 : |a 2 - b 1| ≤ |a 2 - b 2| := h 2 1 2 (by decide)
  rw [e]
  rcases psl3f201_ps3_perm_cases σ with rfl | rfl | rfl | rfl | rfl | rfl
  · have hc : ∑ i, |a i - b (psl3f201_PS3P012 i)| = |a 0 - b 0| + |a 1 - b 1| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [p00, p20, p21, abs_nonneg (a 0 - b 0), abs_nonneg (a 1 - b 1), abs_nonneg (a 2 - b 2)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P021 i)| = |a 0 - b 0| + |a 1 - b 2| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [p00, p10, p20, abs_nonneg (a 0 - b 0), abs_nonneg (a 1 - b 2), abs_nonneg (a 2 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P102 i)| = |a 0 - b 1| + |a 1 - b 0| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [p00, p01, p10, p11, p20, p21, abs_nonneg (a 0 - b 1), abs_nonneg (a 1 - b 0), abs_nonneg (a 2 - b 2)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P120 i)| = |a 0 - b 1| + |a 1 - b 2| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [p00, p01, p10, abs_nonneg (a 0 - b 1), abs_nonneg (a 1 - b 2), abs_nonneg (a 2 - b 0)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P201 i)| = |a 0 - b 2| + |a 1 - b 0| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [p10, p11, p20, abs_nonneg (a 0 - b 2), abs_nonneg (a 1 - b 0), abs_nonneg (a 2 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P210 i)| = |a 0 - b 2| + |a 1 - b 1| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [abs_nonneg (a 0 - b 2), abs_nonneg (a 1 - b 1), abs_nonneg (a 2 - b 0)]

theorem psl3f201_ps3_case_201_120_021 (a b : Fin 3 → ℝ)
    (h : is_line_distance_preference_profile a b ![psl3f201_PS3P201, psl3f201_PS3P120, psl3f201_PS3P021]) (σ : Equiv.Perm (Fin 3)) :
    probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P120, psl3f201_PS3P021] ≤ 3 * ∑ i, |a i - b (σ i)| := by
  have hX : ((psl3f201_psPhaseQ 3 ![psl3f201_PS3P201, psl3f201_PS3P120, psl3f201_PS3P021])^[3] (fun _ => 1, fun _ _ => 0)).2 = ![![(0 : ℚ), (0 : ℚ), (1 : ℚ)], ![(0 : ℚ), (1 : ℚ), (0 : ℚ)], ![(1 : ℚ), (0 : ℚ), (0 : ℚ)]] := by decide +kernel
  have e : probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P120, psl3f201_PS3P021] = (1/1 : ℝ) * |a 0 - b 2| + (1/1 : ℝ) * |a 1 - b 1| + (1/1 : ℝ) * |a 2 - b 0| := by
    unfold probabilistic_serial_line_cost
    simp only [psl3f201_psQ_cast, hX, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    push_cast; ring
  have p00 : |a 0 - b 2| ≤ |a 0 - b 0| := h 0 0 1 (by decide)
  have p01 : |a 0 - b 0| ≤ |a 0 - b 1| := h 0 1 2 (by decide)
  have p10 : |a 1 - b 1| ≤ |a 1 - b 2| := h 1 0 1 (by decide)
  have p11 : |a 1 - b 2| ≤ |a 1 - b 0| := h 1 1 2 (by decide)
  have p20 : |a 2 - b 0| ≤ |a 2 - b 2| := h 2 0 1 (by decide)
  have p21 : |a 2 - b 2| ≤ |a 2 - b 1| := h 2 1 2 (by decide)
  rw [e]
  rcases psl3f201_ps3_perm_cases σ with rfl | rfl | rfl | rfl | rfl | rfl
  · have hc : ∑ i, |a i - b (psl3f201_PS3P012 i)| = |a 0 - b 0| + |a 1 - b 1| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [p00, p20, abs_nonneg (a 0 - b 0), abs_nonneg (a 1 - b 1), abs_nonneg (a 2 - b 2)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P021 i)| = |a 0 - b 0| + |a 1 - b 2| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [p00, p10, p20, p21, abs_nonneg (a 0 - b 0), abs_nonneg (a 1 - b 2), abs_nonneg (a 2 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P102 i)| = |a 0 - b 1| + |a 1 - b 0| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [p00, p01, p10, p11, p20, abs_nonneg (a 0 - b 1), abs_nonneg (a 1 - b 0), abs_nonneg (a 2 - b 2)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P120 i)| = |a 0 - b 1| + |a 1 - b 2| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [p00, p01, p10, abs_nonneg (a 0 - b 1), abs_nonneg (a 1 - b 2), abs_nonneg (a 2 - b 0)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P201 i)| = |a 0 - b 2| + |a 1 - b 0| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [p10, p11, p20, p21, abs_nonneg (a 0 - b 2), abs_nonneg (a 1 - b 0), abs_nonneg (a 2 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P210 i)| = |a 0 - b 2| + |a 1 - b 1| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [abs_nonneg (a 0 - b 2), abs_nonneg (a 1 - b 1), abs_nonneg (a 2 - b 0)]

theorem psl3f201_ps3_case_201_120_102 (a b : Fin 3 → ℝ)
    (h : is_line_distance_preference_profile a b ![psl3f201_PS3P201, psl3f201_PS3P120, psl3f201_PS3P102]) (σ : Equiv.Perm (Fin 3)) :
    probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P120, psl3f201_PS3P102] ≤ 3 * ∑ i, |a i - b (σ i)| := by
  have hX : ((psl3f201_psPhaseQ 3 ![psl3f201_PS3P201, psl3f201_PS3P120, psl3f201_PS3P102])^[3] (fun _ => 1, fun _ _ => 0)).2 = ![![(1/4 : ℚ), (0 : ℚ), (3/4 : ℚ)], ![(1/4 : ℚ), (1/2 : ℚ), (1/4 : ℚ)], ![(1/2 : ℚ), (1/2 : ℚ), (0 : ℚ)]] := by decide +kernel
  have e : probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P120, psl3f201_PS3P102] = (1/4 : ℝ) * |a 0 - b 0| + (3/4 : ℝ) * |a 0 - b 2| + (1/4 : ℝ) * |a 1 - b 0| + (1/2 : ℝ) * |a 1 - b 1| + (1/4 : ℝ) * |a 1 - b 2| + (1/2 : ℝ) * |a 2 - b 0| + (1/2 : ℝ) * |a 2 - b 1| := by
    unfold probabilistic_serial_line_cost
    simp only [psl3f201_psQ_cast, hX, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    push_cast; ring
  have p00 : |a 0 - b 2| ≤ |a 0 - b 0| := h 0 0 1 (by decide)
  have p01 : |a 0 - b 0| ≤ |a 0 - b 1| := h 0 1 2 (by decide)
  have p10 : |a 1 - b 1| ≤ |a 1 - b 2| := h 1 0 1 (by decide)
  have p11 : |a 1 - b 2| ≤ |a 1 - b 0| := h 1 1 2 (by decide)
  have p20 : |a 2 - b 1| ≤ |a 2 - b 0| := h 2 0 1 (by decide)
  have p21 : |a 2 - b 0| ≤ |a 2 - b 2| := h 2 1 2 (by decide)
  rw [e]
  rcases psl3f201_ps3_perm_cases σ with rfl | rfl | rfl | rfl | rfl | rfl
  · have hc : ∑ i, |a i - b (psl3f201_PS3P012 i)| = |a 0 - b 0| + |a 1 - b 1| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triB (a 1) (a 2) (b 1), psl3f201_triC (a 1) (a 2) (b 2), psl3f201_triB (a 1) (b 0) (b 1), psl3f201_triC (a 1) (b 1) (b 2), psl3f201_triA (a 1) (b 1) (b 2), psl3f201_triA (a 2) (b 0) (b 1), p00, p20, p21, abs_nonneg (a 0 - b 0), abs_nonneg (a 1 - b 1), abs_nonneg (a 2 - b 2)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P021 i)| = |a 0 - b 0| + |a 1 - b 2| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triA (a 0) (b 0) (b 2), psl3f201_triB (a 1) (a 2) (b 1), psl3f201_triA (a 1) (a 2) (b 2), psl3f201_triC (a 1) (b 0) (b 2), psl3f201_triB (a 1) (b 0) (b 2), p00, p10, p21, abs_nonneg (a 2 - b 1), abs_nonneg (a 0 - b 0), abs_nonneg (a 1 - b 2)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P102 i)| = |a 0 - b 1| + |a 1 - b 0| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [p00, p01, p10, p11, p20, p21, abs_nonneg (a 0 - b 1), abs_nonneg (a 1 - b 0), abs_nonneg (a 2 - b 2)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P120 i)| = |a 0 - b 1| + |a 1 - b 2| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triA (a 0) (b 0) (b 2), psl3f201_triC (a 1) (a 2) (b 0), psl3f201_triB (a 1) (a 2) (b 1), psl3f201_triB (a 1) (b 0) (b 2), p00, p01, p10, p20, abs_nonneg (a 1 - b 1), abs_nonneg (a 0 - b 1), abs_nonneg (a 1 - b 2), abs_nonneg (a 2 - b 0)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P201 i)| = |a 0 - b 2| + |a 1 - b 0| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triB (a 0) (b 0) (b 2), psl3f201_triA (a 1) (b 0) (b 1), psl3f201_triA (a 1) (b 0) (b 2), psl3f201_triB (a 2) (b 0) (b 1), p10, p11, abs_nonneg (a 0 - b 2), abs_nonneg (a 2 - b 1), abs_nonneg (a 1 - b 0)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P210 i)| = |a 0 - b 2| + |a 1 - b 1| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triB (a 0) (b 1) (b 2), psl3f201_triB (a 1) (b 0) (b 1), psl3f201_triA (a 1) (b 1) (b 2), psl3f201_triA (a 2) (b 0) (b 1), p01, p11, p20, abs_nonneg (a 0 - b 2), abs_nonneg (a 1 - b 1), abs_nonneg (a 2 - b 0)]

theorem psl3f201_ps3_case_201_120_120 (a b : Fin 3 → ℝ)
    (h : is_line_distance_preference_profile a b ![psl3f201_PS3P201, psl3f201_PS3P120, psl3f201_PS3P120]) (σ : Equiv.Perm (Fin 3)) :
    probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P120, psl3f201_PS3P120] ≤ 3 * ∑ i, |a i - b (σ i)| := by
  have hX : ((psl3f201_psPhaseQ 3 ![psl3f201_PS3P201, psl3f201_PS3P120, psl3f201_PS3P120])^[3] (fun _ => 1, fun _ _ => 0)).2 = ![![(1/3 : ℚ), (0 : ℚ), (2/3 : ℚ)], ![(1/3 : ℚ), (1/2 : ℚ), (1/6 : ℚ)], ![(1/3 : ℚ), (1/2 : ℚ), (1/6 : ℚ)]] := by decide +kernel
  have e : probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P120, psl3f201_PS3P120] = (1/3 : ℝ) * |a 0 - b 0| + (2/3 : ℝ) * |a 0 - b 2| + (1/3 : ℝ) * |a 1 - b 0| + (1/2 : ℝ) * |a 1 - b 1| + (1/6 : ℝ) * |a 1 - b 2| + (1/3 : ℝ) * |a 2 - b 0| + (1/2 : ℝ) * |a 2 - b 1| + (1/6 : ℝ) * |a 2 - b 2| := by
    unfold probabilistic_serial_line_cost
    simp only [psl3f201_psQ_cast, hX, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    push_cast; ring
  have p00 : |a 0 - b 2| ≤ |a 0 - b 0| := h 0 0 1 (by decide)
  have p01 : |a 0 - b 0| ≤ |a 0 - b 1| := h 0 1 2 (by decide)
  have p10 : |a 1 - b 1| ≤ |a 1 - b 2| := h 1 0 1 (by decide)
  have p11 : |a 1 - b 2| ≤ |a 1 - b 0| := h 1 1 2 (by decide)
  have p20 : |a 2 - b 1| ≤ |a 2 - b 2| := h 2 0 1 (by decide)
  have p21 : |a 2 - b 2| ≤ |a 2 - b 0| := h 2 1 2 (by decide)
  rw [e]
  rcases psl3f201_ps3_perm_cases σ with rfl | rfl | rfl | rfl | rfl | rfl
  · have hc : ∑ i, |a i - b (psl3f201_PS3P012 i)| = |a 0 - b 0| + |a 1 - b 1| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triA (a 0) (a 2) (b 0), psl3f201_triB (a 0) (a 2) (b 2), psl3f201_triA (a 0) (b 0) (b 1), psl3f201_triB (a 0) (b 1) (b 2), psl3f201_triB (a 1) (b 0) (b 1), psl3f201_triA (a 1) (b 0) (b 1), psl3f201_triB (a 1) (b 0) (b 2), psl3f201_triA (a 1) (b 0) (b 2), psl3f201_triC (a 1) (b 1) (b 2), psl3f201_triA (a 2) (b 1) (b 2), p00, p20, abs_nonneg (a 0 - b 0), abs_nonneg (a 1 - b 1), abs_nonneg (a 2 - b 2)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P021 i)| = |a 0 - b 0| + |a 1 - b 2| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triC (a 0) (a 1) (b 1), psl3f201_triB (a 0) (a 1) (b 2), psl3f201_triA (a 0) (a 2) (b 0), psl3f201_triB (a 0) (a 2) (b 1), psl3f201_triA (a 0) (b 0) (b 2), psl3f201_triB (a 1) (a 2) (b 1), psl3f201_triA (a 1) (a 2) (b 2), psl3f201_triB (a 1) (b 0) (b 2), p00, p10, abs_nonneg (a 1 - b 2), abs_nonneg (a 2 - b 1), abs_nonneg (a 0 - b 0)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P102 i)| = |a 0 - b 1| + |a 1 - b 0| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triA (a 0) (b 0) (b 1), psl3f201_triA (a 1) (a 2) (b 0), psl3f201_triC (a 1) (a 2) (b 1), psl3f201_triB (a 1) (a 2) (b 2), psl3f201_triB (a 2) (b 0) (b 1), p00, p01, p10, p11, p20, abs_nonneg (a 0 - b 1), abs_nonneg (a 1 - b 0), abs_nonneg (a 2 - b 2)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P120 i)| = |a 0 - b 1| + |a 1 - b 2| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triA (a 0) (a 1) (b 0), psl3f201_triB (a 0) (a 1) (b 1), psl3f201_triC (a 1) (a 2) (b 0), psl3f201_triB (a 1) (a 2) (b 1), psl3f201_triB (a 1) (b 0) (b 1), psl3f201_triA (a 1) (b 0) (b 1), p00, p01, p10, p20, p21, abs_nonneg (a 0 - b 1), abs_nonneg (a 1 - b 2), abs_nonneg (a 2 - b 0)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P201 i)| = |a 0 - b 2| + |a 1 - b 0| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triC (a 0) (a 1) (b 0), psl3f201_triB (a 0) (a 1) (b 2), psl3f201_triA (a 1) (b 0) (b 1), psl3f201_triB (a 2) (b 0) (b 1), p10, p11, p21, abs_nonneg (a 0 - b 2), abs_nonneg (a 2 - b 1), abs_nonneg (a 1 - b 0)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P210 i)| = |a 0 - b 2| + |a 1 - b 1| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triB (a 0) (b 0) (b 2), psl3f201_triB (a 1) (b 0) (b 1), psl3f201_triC (a 1) (b 1) (b 2), psl3f201_triA (a 1) (b 1) (b 2), psl3f201_triA (a 2) (b 0) (b 1), psl3f201_triA (a 2) (b 0) (b 2), p11, p20, p21, abs_nonneg (a 0 - b 2), abs_nonneg (a 1 - b 1), abs_nonneg (a 2 - b 0)]

theorem psl3f201_ps3_case_201_120_201 (a b : Fin 3 → ℝ)
    (h : is_line_distance_preference_profile a b ![psl3f201_PS3P201, psl3f201_PS3P120, psl3f201_PS3P201]) (σ : Equiv.Perm (Fin 3)) :
    probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P120, psl3f201_PS3P201] ≤ 3 * ∑ i, |a i - b (σ i)| := by
  have hX : ((psl3f201_psPhaseQ 3 ![psl3f201_PS3P201, psl3f201_PS3P120, psl3f201_PS3P201])^[3] (fun _ => 1, fun _ _ => 0)).2 = ![![(1/2 : ℚ), (0 : ℚ), (1/2 : ℚ)], ![(0 : ℚ), (1 : ℚ), (0 : ℚ)], ![(1/2 : ℚ), (0 : ℚ), (1/2 : ℚ)]] := by decide +kernel
  have e : probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P120, psl3f201_PS3P201] = (1/2 : ℝ) * |a 0 - b 0| + (1/2 : ℝ) * |a 0 - b 2| + (1/1 : ℝ) * |a 1 - b 1| + (1/2 : ℝ) * |a 2 - b 0| + (1/2 : ℝ) * |a 2 - b 2| := by
    unfold probabilistic_serial_line_cost
    simp only [psl3f201_psQ_cast, hX, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    push_cast; ring
  have p00 : |a 0 - b 2| ≤ |a 0 - b 0| := h 0 0 1 (by decide)
  have p01 : |a 0 - b 0| ≤ |a 0 - b 1| := h 0 1 2 (by decide)
  have p10 : |a 1 - b 1| ≤ |a 1 - b 2| := h 1 0 1 (by decide)
  have p11 : |a 1 - b 2| ≤ |a 1 - b 0| := h 1 1 2 (by decide)
  have p20 : |a 2 - b 2| ≤ |a 2 - b 0| := h 2 0 1 (by decide)
  have p21 : |a 2 - b 0| ≤ |a 2 - b 1| := h 2 1 2 (by decide)
  rw [e]
  rcases psl3f201_ps3_perm_cases σ with rfl | rfl | rfl | rfl | rfl | rfl
  · have hc : ∑ i, |a i - b (psl3f201_PS3P012 i)| = |a 0 - b 0| + |a 1 - b 1| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triA (a 0) (b 0) (b 2), psl3f201_triB (a 2) (b 0) (b 2), p00, abs_nonneg (a 1 - b 1), abs_nonneg (a 2 - b 2), abs_nonneg (a 0 - b 0)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P021 i)| = |a 0 - b 0| + |a 1 - b 2| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [p00, p10, p20, p21, abs_nonneg (a 0 - b 0), abs_nonneg (a 1 - b 2), abs_nonneg (a 2 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P102 i)| = |a 0 - b 1| + |a 1 - b 0| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triA (a 0) (b 0) (b 2), psl3f201_triA (a 1) (b 0) (b 2), psl3f201_triB (a 2) (b 0) (b 2), p00, p01, p10, p11, abs_nonneg (a 2 - b 2), abs_nonneg (a 0 - b 1), abs_nonneg (a 1 - b 0)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P120 i)| = |a 0 - b 1| + |a 1 - b 2| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [p00, p01, p10, p20, abs_nonneg (a 0 - b 1), abs_nonneg (a 1 - b 2), abs_nonneg (a 2 - b 0)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P201 i)| = |a 0 - b 2| + |a 1 - b 0| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triC (a 0) (a 1) (b 0), psl3f201_triB (a 0) (a 1) (b 2), psl3f201_triB (a 0) (a 2) (b 2), psl3f201_triA (a 0) (a 2) (b 2), psl3f201_triB (a 0) (b 0) (b 2), psl3f201_triA (a 2) (b 0) (b 2), p10, p11, p20, p21, abs_nonneg (a 0 - b 2), abs_nonneg (a 1 - b 0), abs_nonneg (a 2 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P210 i)| = |a 0 - b 2| + |a 1 - b 1| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triC (a 0) (a 2) (b 0), psl3f201_triB (a 0) (a 2) (b 2), p20, abs_nonneg (a 0 - b 2), abs_nonneg (a 1 - b 1), abs_nonneg (a 2 - b 0)]

theorem psl3f201_ps3_case_201_120_210 (a b : Fin 3 → ℝ)
    (h : is_line_distance_preference_profile a b ![psl3f201_PS3P201, psl3f201_PS3P120, psl3f201_PS3P210]) (σ : Equiv.Perm (Fin 3)) :
    probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P120, psl3f201_PS3P210] ≤ 3 * ∑ i, |a i - b (σ i)| := by
  have hX : ((psl3f201_psPhaseQ 3 ![psl3f201_PS3P201, psl3f201_PS3P120, psl3f201_PS3P210])^[3] (fun _ => 1, fun _ _ => 0)).2 = ![![(1/2 : ℚ), (0 : ℚ), (1/2 : ℚ)], ![(1/4 : ℚ), (3/4 : ℚ), (0 : ℚ)], ![(1/4 : ℚ), (1/4 : ℚ), (1/2 : ℚ)]] := by decide +kernel
  have e : probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P120, psl3f201_PS3P210] = (1/2 : ℝ) * |a 0 - b 0| + (1/2 : ℝ) * |a 0 - b 2| + (1/4 : ℝ) * |a 1 - b 0| + (3/4 : ℝ) * |a 1 - b 1| + (1/4 : ℝ) * |a 2 - b 0| + (1/4 : ℝ) * |a 2 - b 1| + (1/2 : ℝ) * |a 2 - b 2| := by
    unfold probabilistic_serial_line_cost
    simp only [psl3f201_psQ_cast, hX, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    push_cast; ring
  have p00 : |a 0 - b 2| ≤ |a 0 - b 0| := h 0 0 1 (by decide)
  have p01 : |a 0 - b 0| ≤ |a 0 - b 1| := h 0 1 2 (by decide)
  have p10 : |a 1 - b 1| ≤ |a 1 - b 2| := h 1 0 1 (by decide)
  have p11 : |a 1 - b 2| ≤ |a 1 - b 0| := h 1 1 2 (by decide)
  have p20 : |a 2 - b 2| ≤ |a 2 - b 1| := h 2 0 1 (by decide)
  have p21 : |a 2 - b 1| ≤ |a 2 - b 0| := h 2 1 2 (by decide)
  rw [e]
  rcases psl3f201_ps3_perm_cases σ with rfl | rfl | rfl | rfl | rfl | rfl
  · have hc : ∑ i, |a i - b (psl3f201_PS3P012 i)| = |a 0 - b 0| + |a 1 - b 1| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triA (a 0) (a 1) (b 0), psl3f201_triB (a 0) (a 1) (b 1), psl3f201_triA (a 0) (a 2) (b 0), psl3f201_triB (a 0) (a 2) (b 2), psl3f201_triB (a 0) (b 1) (b 2), psl3f201_triA (a 2) (b 1) (b 2), p00, p21, abs_nonneg (a 1 - b 1), abs_nonneg (a 2 - b 2), abs_nonneg (a 0 - b 0)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P021 i)| = |a 0 - b 0| + |a 1 - b 2| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triC (a 0) (a 1) (a 2), psl3f201_triB (a 0) (a 1) (b 2), psl3f201_triA (a 0) (a 2) (b 0), psl3f201_triB (a 1) (a 2) (b 1), psl3f201_triB (a 1) (b 0) (b 2), psl3f201_triA (a 2) (b 0) (b 2), p00, p10, p20, abs_nonneg (a 2 - b 1), abs_nonneg (a 0 - b 0), abs_nonneg (a 1 - b 2)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P102 i)| = |a 0 - b 1| + |a 1 - b 0| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triA (a 0) (a 2) (b 0), psl3f201_triC (a 0) (a 2) (b 2), psl3f201_triB (a 0) (a 2) (b 2), psl3f201_triA (a 1) (b 0) (b 2), psl3f201_triB (a 2) (b 0) (b 2), p00, p01, p10, p11, p21, abs_nonneg (a 0 - b 1), abs_nonneg (a 1 - b 0), abs_nonneg (a 2 - b 2)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P120 i)| = |a 0 - b 1| + |a 1 - b 2| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triA (a 0) (a 1) (b 0), psl3f201_triB (a 0) (a 1) (b 1), psl3f201_triC (a 1) (a 2) (b 0), psl3f201_triB (a 1) (a 2) (b 2), p00, p01, p10, p20, p21, abs_nonneg (a 1 - b 2), abs_nonneg (a 0 - b 1), abs_nonneg (a 2 - b 0)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P201 i)| = |a 0 - b 2| + |a 1 - b 0| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triC (a 0) (a 1) (b 0), psl3f201_triB (a 0) (a 1) (b 2), psl3f201_triC (a 0) (a 2) (b 1), psl3f201_triB (a 0) (a 2) (b 2), psl3f201_triA (a 1) (b 0) (b 2), psl3f201_triB (a 2) (b 0) (b 2), p01, p10, p11, p20, abs_nonneg (a 0 - b 2), abs_nonneg (a 1 - b 0), abs_nonneg (a 2 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P210 i)| = |a 0 - b 2| + |a 1 - b 1| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triB (a 0) (b 0) (b 2), psl3f201_triC (a 1) (a 2) (b 0), psl3f201_triB (a 1) (a 2) (b 1), psl3f201_triA (a 2) (b 0) (b 2), p20, p21, abs_nonneg (a 0 - b 2), abs_nonneg (a 1 - b 1), abs_nonneg (a 2 - b 0)]

theorem psl3f201_ps3_case_201_201_012 (a b : Fin 3 → ℝ)
    (h : is_line_distance_preference_profile a b ![psl3f201_PS3P201, psl3f201_PS3P201, psl3f201_PS3P012]) (σ : Equiv.Perm (Fin 3)) :
    probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P201, psl3f201_PS3P012] ≤ 3 * ∑ i, |a i - b (σ i)| := by
  have hX : ((psl3f201_psPhaseQ 3 ![psl3f201_PS3P201, psl3f201_PS3P201, psl3f201_PS3P012])^[3] (fun _ => 1, fun _ _ => 0)).2 = ![![(1/6 : ℚ), (1/3 : ℚ), (1/2 : ℚ)], ![(1/6 : ℚ), (1/3 : ℚ), (1/2 : ℚ)], ![(2/3 : ℚ), (1/3 : ℚ), (0 : ℚ)]] := by decide +kernel
  have e : probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P201, psl3f201_PS3P012] = (1/6 : ℝ) * |a 0 - b 0| + (1/3 : ℝ) * |a 0 - b 1| + (1/2 : ℝ) * |a 0 - b 2| + (1/6 : ℝ) * |a 1 - b 0| + (1/3 : ℝ) * |a 1 - b 1| + (1/2 : ℝ) * |a 1 - b 2| + (2/3 : ℝ) * |a 2 - b 0| + (1/3 : ℝ) * |a 2 - b 1| := by
    unfold probabilistic_serial_line_cost
    simp only [psl3f201_psQ_cast, hX, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    push_cast; ring
  have p00 : |a 0 - b 2| ≤ |a 0 - b 0| := h 0 0 1 (by decide)
  have p01 : |a 0 - b 0| ≤ |a 0 - b 1| := h 0 1 2 (by decide)
  have p10 : |a 1 - b 2| ≤ |a 1 - b 0| := h 1 0 1 (by decide)
  have p11 : |a 1 - b 0| ≤ |a 1 - b 1| := h 1 1 2 (by decide)
  have p20 : |a 2 - b 0| ≤ |a 2 - b 1| := h 2 0 1 (by decide)
  have p21 : |a 2 - b 1| ≤ |a 2 - b 2| := h 2 1 2 (by decide)
  rw [e]
  rcases psl3f201_ps3_perm_cases σ with rfl | rfl | rfl | rfl | rfl | rfl
  · have hc : ∑ i, |a i - b (psl3f201_PS3P012 i)| = |a 0 - b 0| + |a 1 - b 1| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triC (a 0) (a 2) (b 1), psl3f201_triB (a 0) (a 2) (b 2), psl3f201_triC (a 0) (b 0) (b 1), psl3f201_triA (a 0) (b 0) (b 2), psl3f201_triA (a 1) (b 0) (b 1), psl3f201_triB (a 2) (b 0) (b 2), p00, p10, p11, p20, p21, abs_nonneg (a 0 - b 0), abs_nonneg (a 1 - b 1), abs_nonneg (a 2 - b 2)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P021 i)| = |a 0 - b 0| + |a 1 - b 2| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triC (a 0) (a 1) (b 2), psl3f201_triB (a 0) (a 1) (b 2), psl3f201_triB (a 0) (a 2) (b 0), psl3f201_triC (a 0) (a 2) (b 1), psl3f201_triA (a 0) (b 0) (b 2), psl3f201_triC (a 1) (a 2) (b 1), psl3f201_triB (a 1) (a 2) (b 2), psl3f201_triB (a 1) (b 0) (b 2), psl3f201_triC (a 2) (b 0) (b 2), p00, p20, abs_nonneg (a 0 - b 0), abs_nonneg (a 1 - b 2), abs_nonneg (a 2 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P102 i)| = |a 0 - b 1| + |a 1 - b 0| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triA (a 0) (b 1) (b 2), psl3f201_triA (a 1) (a 2) (b 0), psl3f201_triC (a 1) (a 2) (b 1), psl3f201_triB (a 1) (a 2) (b 2), psl3f201_triB (a 1) (b 1) (b 2), p00, p01, p10, p20, p21, abs_nonneg (a 0 - b 1), abs_nonneg (a 1 - b 0), abs_nonneg (a 2 - b 2)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P120 i)| = |a 0 - b 1| + |a 1 - b 2| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triA (a 0) (a 1) (b 0), psl3f201_triB (a 0) (a 1) (b 2), psl3f201_triA (a 0) (b 0) (b 1), psl3f201_triA (a 0) (b 1) (b 2), psl3f201_triB (a 1) (b 1) (b 2), psl3f201_triC (a 2) (b 0) (b 1), p00, p01, abs_nonneg (a 1 - b 2), abs_nonneg (a 2 - b 0), abs_nonneg (a 0 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P201 i)| = |a 0 - b 2| + |a 1 - b 0| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triB (a 0) (a 1) (b 2), psl3f201_triA (a 0) (a 1) (b 2), psl3f201_triC (a 0) (b 0) (b 2), psl3f201_triB (a 0) (b 0) (b 2), psl3f201_triB (a 0) (b 1) (b 2), psl3f201_triB (a 1) (a 2) (b 0), psl3f201_triC (a 1) (a 2) (b 1), psl3f201_triA (a 1) (b 0) (b 2), psl3f201_triA (a 1) (b 1) (b 2), p10, p20, abs_nonneg (a 0 - b 2), abs_nonneg (a 1 - b 0), abs_nonneg (a 2 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P210 i)| = |a 0 - b 2| + |a 1 - b 1| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triC (a 0) (a 2) (b 0), psl3f201_triB (a 0) (a 2) (b 2), psl3f201_triB (a 0) (b 1) (b 2), psl3f201_triC (a 1) (a 2) (b 0), psl3f201_triB (a 1) (a 2) (b 0), psl3f201_triA (a 1) (a 2) (b 1), psl3f201_triA (a 1) (a 2) (b 2), psl3f201_triA (a 1) (b 1) (b 2), p10, p11, abs_nonneg (a 0 - b 2), abs_nonneg (a 1 - b 1), abs_nonneg (a 2 - b 0)]

theorem psl3f201_ps3_case_201_201_021 (a b : Fin 3 → ℝ)
    (h : is_line_distance_preference_profile a b ![psl3f201_PS3P201, psl3f201_PS3P201, psl3f201_PS3P021]) (σ : Equiv.Perm (Fin 3)) :
    probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P201, psl3f201_PS3P021] ≤ 3 * ∑ i, |a i - b (σ i)| := by
  have hX : ((psl3f201_psPhaseQ 3 ![psl3f201_PS3P201, psl3f201_PS3P201, psl3f201_PS3P021])^[3] (fun _ => 1, fun _ _ => 0)).2 = ![![(1/6 : ℚ), (1/3 : ℚ), (1/2 : ℚ)], ![(1/6 : ℚ), (1/3 : ℚ), (1/2 : ℚ)], ![(2/3 : ℚ), (1/3 : ℚ), (0 : ℚ)]] := by decide +kernel
  have e : probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P201, psl3f201_PS3P021] = (1/6 : ℝ) * |a 0 - b 0| + (1/3 : ℝ) * |a 0 - b 1| + (1/2 : ℝ) * |a 0 - b 2| + (1/6 : ℝ) * |a 1 - b 0| + (1/3 : ℝ) * |a 1 - b 1| + (1/2 : ℝ) * |a 1 - b 2| + (2/3 : ℝ) * |a 2 - b 0| + (1/3 : ℝ) * |a 2 - b 1| := by
    unfold probabilistic_serial_line_cost
    simp only [psl3f201_psQ_cast, hX, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    push_cast; ring
  have p00 : |a 0 - b 2| ≤ |a 0 - b 0| := h 0 0 1 (by decide)
  have p01 : |a 0 - b 0| ≤ |a 0 - b 1| := h 0 1 2 (by decide)
  have p10 : |a 1 - b 2| ≤ |a 1 - b 0| := h 1 0 1 (by decide)
  have p11 : |a 1 - b 0| ≤ |a 1 - b 1| := h 1 1 2 (by decide)
  have p20 : |a 2 - b 0| ≤ |a 2 - b 2| := h 2 0 1 (by decide)
  have p21 : |a 2 - b 2| ≤ |a 2 - b 1| := h 2 1 2 (by decide)
  rw [e]
  rcases psl3f201_ps3_perm_cases σ with rfl | rfl | rfl | rfl | rfl | rfl
  · have hc : ∑ i, |a i - b (psl3f201_PS3P012 i)| = |a 0 - b 0| + |a 1 - b 1| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triC (a 0) (b 0) (b 1), psl3f201_triA (a 0) (b 1) (b 2), psl3f201_triB (a 1) (a 2) (b 0), psl3f201_triC (a 1) (a 2) (b 2), psl3f201_triA (a 1) (b 0) (b 1), psl3f201_triB (a 2) (b 1) (b 2), p00, p11, p20, abs_nonneg (a 0 - b 2), abs_nonneg (a 2 - b 0), abs_nonneg (a 0 - b 0), abs_nonneg (a 1 - b 1), abs_nonneg (a 2 - b 2)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P021 i)| = |a 0 - b 0| + |a 1 - b 2| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triC (a 0) (b 0) (b 1), psl3f201_triA (a 0) (b 0) (b 2), psl3f201_triC (a 1) (a 2) (b 1), psl3f201_triB (a 1) (a 2) (b 2), psl3f201_triA (a 1) (b 0) (b 1), psl3f201_triC (a 1) (b 0) (b 2), psl3f201_triB (a 1) (b 0) (b 2), psl3f201_triA (a 1) (b 0) (b 2), p00, p20, p21, abs_nonneg (a 0 - b 0), abs_nonneg (a 1 - b 2), abs_nonneg (a 2 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P102 i)| = |a 0 - b 1| + |a 1 - b 0| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triA (a 0) (b 1) (b 2), psl3f201_triB (a 1) (b 1) (b 2), psl3f201_triB (a 2) (b 1) (b 2), p00, p01, p10, p20, abs_nonneg (a 1 - b 0), abs_nonneg (a 2 - b 2), abs_nonneg (a 0 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P120 i)| = |a 0 - b 1| + |a 1 - b 2| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triA (a 0) (a 1) (b 0), psl3f201_triB (a 0) (a 1) (b 2), psl3f201_triA (a 0) (b 0) (b 1), psl3f201_triA (a 0) (b 1) (b 2), psl3f201_triB (a 1) (b 1) (b 2), psl3f201_triC (a 2) (b 0) (b 1), p00, p01, abs_nonneg (a 1 - b 2), abs_nonneg (a 2 - b 0), abs_nonneg (a 0 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P201 i)| = |a 0 - b 2| + |a 1 - b 0| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triC (a 0) (a 1) (b 0), psl3f201_triB (a 0) (a 1) (b 2), psl3f201_triC (a 0) (a 2) (b 1), psl3f201_triB (a 0) (a 2) (b 2), psl3f201_triC (a 1) (a 2) (b 1), psl3f201_triB (a 1) (a 2) (b 2), p10, p20, p21, abs_nonneg (a 0 - b 2), abs_nonneg (a 1 - b 0), abs_nonneg (a 2 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P210 i)| = |a 0 - b 2| + |a 1 - b 1| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triC (a 0) (a 2) (b 0), psl3f201_triB (a 0) (a 2) (b 2), psl3f201_triB (a 0) (b 1) (b 2), psl3f201_triC (a 1) (a 2) (b 0), psl3f201_triB (a 1) (a 2) (b 0), psl3f201_triA (a 1) (a 2) (b 1), psl3f201_triA (a 1) (b 1) (b 2), p10, p11, p21, abs_nonneg (a 0 - b 2), abs_nonneg (a 1 - b 1), abs_nonneg (a 2 - b 0)]

theorem psl3f201_ps3_case_201_201_102 (a b : Fin 3 → ℝ)
    (h : is_line_distance_preference_profile a b ![psl3f201_PS3P201, psl3f201_PS3P201, psl3f201_PS3P102]) (σ : Equiv.Perm (Fin 3)) :
    probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P201, psl3f201_PS3P102] ≤ 3 * ∑ i, |a i - b (σ i)| := by
  have hX : ((psl3f201_psPhaseQ 3 ![psl3f201_PS3P201, psl3f201_PS3P201, psl3f201_PS3P102])^[3] (fun _ => 1, fun _ _ => 0)).2 = ![![(1/2 : ℚ), (0 : ℚ), (1/2 : ℚ)], ![(1/2 : ℚ), (0 : ℚ), (1/2 : ℚ)], ![(0 : ℚ), (1 : ℚ), (0 : ℚ)]] := by decide +kernel
  have e : probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P201, psl3f201_PS3P102] = (1/2 : ℝ) * |a 0 - b 0| + (1/2 : ℝ) * |a 0 - b 2| + (1/2 : ℝ) * |a 1 - b 0| + (1/2 : ℝ) * |a 1 - b 2| + (1/1 : ℝ) * |a 2 - b 1| := by
    unfold probabilistic_serial_line_cost
    simp only [psl3f201_psQ_cast, hX, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    push_cast; ring
  have p00 : |a 0 - b 2| ≤ |a 0 - b 0| := h 0 0 1 (by decide)
  have p01 : |a 0 - b 0| ≤ |a 0 - b 1| := h 0 1 2 (by decide)
  have p10 : |a 1 - b 2| ≤ |a 1 - b 0| := h 1 0 1 (by decide)
  have p11 : |a 1 - b 0| ≤ |a 1 - b 1| := h 1 1 2 (by decide)
  have p20 : |a 2 - b 1| ≤ |a 2 - b 0| := h 2 0 1 (by decide)
  have p21 : |a 2 - b 0| ≤ |a 2 - b 2| := h 2 1 2 (by decide)
  rw [e]
  rcases psl3f201_ps3_perm_cases σ with rfl | rfl | rfl | rfl | rfl | rfl
  · have hc : ∑ i, |a i - b (psl3f201_PS3P012 i)| = |a 0 - b 0| + |a 1 - b 1| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [p00, p10, p11, p20, p21, abs_nonneg (a 0 - b 0), abs_nonneg (a 1 - b 1), abs_nonneg (a 2 - b 2)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P021 i)| = |a 0 - b 0| + |a 1 - b 2| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triA (a 0) (a 1) (b 0), psl3f201_triB (a 0) (a 1) (b 2), p00, abs_nonneg (a 1 - b 2), abs_nonneg (a 2 - b 1), abs_nonneg (a 0 - b 0)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P102 i)| = |a 0 - b 1| + |a 1 - b 0| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [p00, p01, p10, p20, p21, abs_nonneg (a 0 - b 1), abs_nonneg (a 1 - b 0), abs_nonneg (a 2 - b 2)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P120 i)| = |a 0 - b 1| + |a 1 - b 2| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triA (a 0) (b 1) (b 2), psl3f201_triB (a 1) (b 1) (b 2), psl3f201_triA (a 1) (b 1) (b 2), p00, p01, p11, p20, abs_nonneg (a 2 - b 0), abs_nonneg (a 0 - b 1), abs_nonneg (a 1 - b 2)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P201 i)| = |a 0 - b 2| + |a 1 - b 0| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triC (a 0) (a 1) (b 0), psl3f201_triB (a 0) (a 1) (b 2), p10, abs_nonneg (a 0 - b 2), abs_nonneg (a 2 - b 1), abs_nonneg (a 1 - b 0)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P210 i)| = |a 0 - b 2| + |a 1 - b 1| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triC (a 0) (a 1) (b 1), psl3f201_triB (a 0) (a 1) (b 2), p01, p10, p11, p20, abs_nonneg (a 0 - b 2), abs_nonneg (a 2 - b 0), abs_nonneg (a 1 - b 1)]

theorem psl3f201_ps3_case_201_201_120 (a b : Fin 3 → ℝ)
    (h : is_line_distance_preference_profile a b ![psl3f201_PS3P201, psl3f201_PS3P201, psl3f201_PS3P120]) (σ : Equiv.Perm (Fin 3)) :
    probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P201, psl3f201_PS3P120] ≤ 3 * ∑ i, |a i - b (σ i)| := by
  have hX : ((psl3f201_psPhaseQ 3 ![psl3f201_PS3P201, psl3f201_PS3P201, psl3f201_PS3P120])^[3] (fun _ => 1, fun _ _ => 0)).2 = ![![(1/2 : ℚ), (0 : ℚ), (1/2 : ℚ)], ![(1/2 : ℚ), (0 : ℚ), (1/2 : ℚ)], ![(0 : ℚ), (1 : ℚ), (0 : ℚ)]] := by decide +kernel
  have e : probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P201, psl3f201_PS3P120] = (1/2 : ℝ) * |a 0 - b 0| + (1/2 : ℝ) * |a 0 - b 2| + (1/2 : ℝ) * |a 1 - b 0| + (1/2 : ℝ) * |a 1 - b 2| + (1/1 : ℝ) * |a 2 - b 1| := by
    unfold probabilistic_serial_line_cost
    simp only [psl3f201_psQ_cast, hX, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    push_cast; ring
  have p00 : |a 0 - b 2| ≤ |a 0 - b 0| := h 0 0 1 (by decide)
  have p01 : |a 0 - b 0| ≤ |a 0 - b 1| := h 0 1 2 (by decide)
  have p10 : |a 1 - b 2| ≤ |a 1 - b 0| := h 1 0 1 (by decide)
  have p11 : |a 1 - b 0| ≤ |a 1 - b 1| := h 1 1 2 (by decide)
  have p20 : |a 2 - b 1| ≤ |a 2 - b 2| := h 2 0 1 (by decide)
  have p21 : |a 2 - b 2| ≤ |a 2 - b 0| := h 2 1 2 (by decide)
  rw [e]
  rcases psl3f201_ps3_perm_cases σ with rfl | rfl | rfl | rfl | rfl | rfl
  · have hc : ∑ i, |a i - b (psl3f201_PS3P012 i)| = |a 0 - b 0| + |a 1 - b 1| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [p00, p10, p11, p20, abs_nonneg (a 0 - b 0), abs_nonneg (a 1 - b 1), abs_nonneg (a 2 - b 2)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P021 i)| = |a 0 - b 0| + |a 1 - b 2| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triA (a 0) (b 0) (b 2), psl3f201_triB (a 1) (b 0) (b 2), p00, abs_nonneg (a 1 - b 2), abs_nonneg (a 2 - b 1), abs_nonneg (a 0 - b 0)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P102 i)| = |a 0 - b 1| + |a 1 - b 0| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [p00, p01, p10, p20, abs_nonneg (a 0 - b 1), abs_nonneg (a 1 - b 0), abs_nonneg (a 2 - b 2)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P120 i)| = |a 0 - b 1| + |a 1 - b 2| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triA (a 0) (b 1) (b 2), psl3f201_triB (a 1) (a 2) (b 2), psl3f201_triA (a 1) (a 2) (b 2), psl3f201_triB (a 1) (b 0) (b 2), psl3f201_triB (a 1) (b 1) (b 2), psl3f201_triA (a 2) (b 0) (b 2), p00, p01, p11, p20, p21, abs_nonneg (a 0 - b 1), abs_nonneg (a 1 - b 2), abs_nonneg (a 2 - b 0)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P201 i)| = |a 0 - b 2| + |a 1 - b 0| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triC (a 0) (a 1) (b 0), psl3f201_triB (a 0) (a 1) (b 2), p10, abs_nonneg (a 0 - b 2), abs_nonneg (a 2 - b 1), abs_nonneg (a 1 - b 0)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P210 i)| = |a 0 - b 2| + |a 1 - b 1| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triB (a 0) (b 0) (b 2), psl3f201_triA (a 1) (b 0) (b 2), psl3f201_triA (a 2) (b 0) (b 2), p10, p11, p20, p21, abs_nonneg (a 0 - b 2), abs_nonneg (a 1 - b 1), abs_nonneg (a 2 - b 0)]

theorem psl3f201_ps3_case_201_201_201 (a b : Fin 3 → ℝ)
    (h : is_line_distance_preference_profile a b ![psl3f201_PS3P201, psl3f201_PS3P201, psl3f201_PS3P201]) (σ : Equiv.Perm (Fin 3)) :
    probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P201, psl3f201_PS3P201] ≤ 3 * ∑ i, |a i - b (σ i)| := by
  have hX : ((psl3f201_psPhaseQ 3 ![psl3f201_PS3P201, psl3f201_PS3P201, psl3f201_PS3P201])^[3] (fun _ => 1, fun _ _ => 0)).2 = ![![(1/3 : ℚ), (1/3 : ℚ), (1/3 : ℚ)], ![(1/3 : ℚ), (1/3 : ℚ), (1/3 : ℚ)], ![(1/3 : ℚ), (1/3 : ℚ), (1/3 : ℚ)]] := by decide +kernel
  have e : probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P201, psl3f201_PS3P201] = (1/3 : ℝ) * |a 0 - b 0| + (1/3 : ℝ) * |a 0 - b 1| + (1/3 : ℝ) * |a 0 - b 2| + (1/3 : ℝ) * |a 1 - b 0| + (1/3 : ℝ) * |a 1 - b 1| + (1/3 : ℝ) * |a 1 - b 2| + (1/3 : ℝ) * |a 2 - b 0| + (1/3 : ℝ) * |a 2 - b 1| + (1/3 : ℝ) * |a 2 - b 2| := by
    unfold probabilistic_serial_line_cost
    simp only [psl3f201_psQ_cast, hX, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    push_cast; ring
  have p00 : |a 0 - b 2| ≤ |a 0 - b 0| := h 0 0 1 (by decide)
  have p01 : |a 0 - b 0| ≤ |a 0 - b 1| := h 0 1 2 (by decide)
  have p10 : |a 1 - b 2| ≤ |a 1 - b 0| := h 1 0 1 (by decide)
  have p11 : |a 1 - b 0| ≤ |a 1 - b 1| := h 1 1 2 (by decide)
  have p20 : |a 2 - b 2| ≤ |a 2 - b 0| := h 2 0 1 (by decide)
  have p21 : |a 2 - b 0| ≤ |a 2 - b 1| := h 2 1 2 (by decide)
  rw [e]
  rcases psl3f201_ps3_perm_cases σ with rfl | rfl | rfl | rfl | rfl | rfl
  · have hc : ∑ i, |a i - b (psl3f201_PS3P012 i)| = |a 0 - b 0| + |a 1 - b 1| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triC (a 0) (b 0) (b 1), psl3f201_triA (a 0) (b 0) (b 2), psl3f201_triA (a 1) (a 2) (b 1), psl3f201_triB (a 1) (a 2) (b 2), psl3f201_triA (a 1) (b 0) (b 1), psl3f201_triB (a 2) (b 0) (b 2), p00, p10, p11, abs_nonneg (a 0 - b 0), abs_nonneg (a 2 - b 2), abs_nonneg (a 1 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P021 i)| = |a 0 - b 0| + |a 1 - b 2| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triA (a 0) (a 1) (b 0), psl3f201_triB (a 0) (a 1) (b 2), psl3f201_triB (a 0) (a 2) (b 0), psl3f201_triC (a 0) (a 2) (b 1), psl3f201_triB (a 1) (a 2) (b 0), psl3f201_triC (a 1) (a 2) (b 1), p00, p20, p21, abs_nonneg (a 1 - b 2), abs_nonneg (a 0 - b 0), abs_nonneg (a 2 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P102 i)| = |a 0 - b 1| + |a 1 - b 0| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triB (a 0) (a 1) (b 0), psl3f201_triA (a 0) (a 1) (b 1), psl3f201_triB (a 0) (a 2) (b 0), psl3f201_triA (a 0) (a 2) (b 1), psl3f201_triA (a 1) (a 2) (b 0), psl3f201_triB (a 1) (a 2) (b 2), p00, p01, p10, abs_nonneg (a 2 - b 2), abs_nonneg (a 0 - b 1), abs_nonneg (a 1 - b 0)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P120 i)| = |a 0 - b 1| + |a 1 - b 2| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triB (a 0) (a 2) (b 0), psl3f201_triA (a 0) (a 2) (b 1), psl3f201_triA (a 0) (b 1) (b 2), psl3f201_triC (a 1) (a 2) (b 0), psl3f201_triB (a 1) (a 2) (b 2), psl3f201_triB (a 1) (b 1) (b 2), p00, p01, p20, abs_nonneg (a 1 - b 2), abs_nonneg (a 2 - b 0), abs_nonneg (a 0 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P201 i)| = |a 0 - b 2| + |a 1 - b 0| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triC (a 0) (a 1) (b 0), psl3f201_triB (a 0) (a 1) (b 2), psl3f201_triB (a 0) (b 1) (b 2), psl3f201_triB (a 1) (a 2) (b 0), psl3f201_triC (a 1) (a 2) (b 1), psl3f201_triA (a 1) (b 1) (b 2), p10, p20, p21, abs_nonneg (a 0 - b 2), abs_nonneg (a 1 - b 0), abs_nonneg (a 2 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P210 i)| = |a 0 - b 2| + |a 1 - b 1| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triC (a 0) (a 2) (b 0), psl3f201_triB (a 0) (a 2) (b 2), psl3f201_triB (a 0) (b 1) (b 2), psl3f201_triB (a 1) (a 2) (b 0), psl3f201_triA (a 1) (a 2) (b 1), psl3f201_triA (a 1) (b 0) (b 1), psl3f201_triA (a 2) (b 0) (b 2), psl3f201_triA (b 0) (b 1) (b 2), p10, p11, p20, abs_nonneg (a 0 - b 2), abs_nonneg (a 1 - b 1), abs_nonneg (a 2 - b 0)]

theorem psl3f201_ps3_case_201_201_210 (a b : Fin 3 → ℝ)
    (h : is_line_distance_preference_profile a b ![psl3f201_PS3P201, psl3f201_PS3P201, psl3f201_PS3P210]) (σ : Equiv.Perm (Fin 3)) :
    probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P201, psl3f201_PS3P210] ≤ 3 * ∑ i, |a i - b (σ i)| := by
  have hX : ((psl3f201_psPhaseQ 3 ![psl3f201_PS3P201, psl3f201_PS3P201, psl3f201_PS3P210])^[3] (fun _ => 1, fun _ _ => 0)).2 = ![![(1/2 : ℚ), (1/6 : ℚ), (1/3 : ℚ)], ![(1/2 : ℚ), (1/6 : ℚ), (1/3 : ℚ)], ![(0 : ℚ), (2/3 : ℚ), (1/3 : ℚ)]] := by decide +kernel
  have e : probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P201, psl3f201_PS3P210] = (1/2 : ℝ) * |a 0 - b 0| + (1/6 : ℝ) * |a 0 - b 1| + (1/3 : ℝ) * |a 0 - b 2| + (1/2 : ℝ) * |a 1 - b 0| + (1/6 : ℝ) * |a 1 - b 1| + (1/3 : ℝ) * |a 1 - b 2| + (2/3 : ℝ) * |a 2 - b 1| + (1/3 : ℝ) * |a 2 - b 2| := by
    unfold probabilistic_serial_line_cost
    simp only [psl3f201_psQ_cast, hX, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    push_cast; ring
  have p00 : |a 0 - b 2| ≤ |a 0 - b 0| := h 0 0 1 (by decide)
  have p01 : |a 0 - b 0| ≤ |a 0 - b 1| := h 0 1 2 (by decide)
  have p10 : |a 1 - b 2| ≤ |a 1 - b 0| := h 1 0 1 (by decide)
  have p11 : |a 1 - b 0| ≤ |a 1 - b 1| := h 1 1 2 (by decide)
  have p20 : |a 2 - b 2| ≤ |a 2 - b 1| := h 2 0 1 (by decide)
  have p21 : |a 2 - b 1| ≤ |a 2 - b 0| := h 2 1 2 (by decide)
  rw [e]
  rcases psl3f201_ps3_perm_cases σ with rfl | rfl | rfl | rfl | rfl | rfl
  · have hc : ∑ i, |a i - b (psl3f201_PS3P012 i)| = |a 0 - b 0| + |a 1 - b 1| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triB (a 0) (a 1) (b 0), psl3f201_triC (a 0) (a 1) (b 1), psl3f201_triA (a 0) (b 0) (b 2), psl3f201_triA (a 1) (b 1) (b 2), psl3f201_triB (a 2) (b 0) (b 2), psl3f201_triB (a 2) (b 1) (b 2), p00, p10, p11, p21, abs_nonneg (a 2 - b 2), abs_nonneg (a 0 - b 0), abs_nonneg (a 1 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P021 i)| = |a 0 - b 0| + |a 1 - b 2| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triA (a 0) (a 1) (b 0), psl3f201_triB (a 0) (a 1) (b 2), psl3f201_triC (a 0) (a 2) (b 1), psl3f201_triB (a 0) (a 2) (b 2), psl3f201_triC (a 1) (a 2) (b 1), psl3f201_triB (a 1) (a 2) (b 2), p00, p11, p20, abs_nonneg (a 1 - b 2), abs_nonneg (a 0 - b 0), abs_nonneg (a 2 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P102 i)| = |a 0 - b 1| + |a 1 - b 0| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triB (a 0) (a 1) (b 0), psl3f201_triA (a 0) (a 1) (b 1), psl3f201_triA (a 0) (b 1) (b 2), psl3f201_triA (a 1) (a 2) (b 0), psl3f201_triB (a 1) (a 2) (b 2), psl3f201_triB (a 2) (b 1) (b 2), p00, p01, p10, p21, abs_nonneg (a 2 - b 2), abs_nonneg (a 0 - b 1), abs_nonneg (a 1 - b 0)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P120 i)| = |a 0 - b 1| + |a 1 - b 2| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triA (a 0) (a 1) (b 1), psl3f201_triB (a 0) (a 1) (b 2), psl3f201_triC (a 1) (a 2) (b 0), psl3f201_triB (a 1) (a 2) (b 2), p00, p01, p11, p20, p21, abs_nonneg (a 1 - b 2), abs_nonneg (a 0 - b 1), abs_nonneg (a 2 - b 0)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P201 i)| = |a 0 - b 2| + |a 1 - b 0| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triC (a 0) (a 2) (b 1), psl3f201_triB (a 0) (a 2) (b 2), psl3f201_triB (a 0) (b 0) (b 2), psl3f201_triA (a 0) (b 1) (b 2), psl3f201_triA (a 1) (b 0) (b 2), psl3f201_triB (a 1) (b 1) (b 2), p01, p10, p20, abs_nonneg (a 0 - b 2), abs_nonneg (a 1 - b 0), abs_nonneg (a 2 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P210 i)| = |a 0 - b 2| + |a 1 - b 1| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triC (a 0) (a 2) (b 0), psl3f201_triB (a 0) (a 2) (b 2), psl3f201_triB (a 0) (b 1) (b 2), psl3f201_triA (a 1) (b 1) (b 2), p01, p10, p11, p20, p21, abs_nonneg (a 0 - b 2), abs_nonneg (a 1 - b 1), abs_nonneg (a 2 - b 0)]

theorem psl3f201_ps3_case_201_210_012 (a b : Fin 3 → ℝ)
    (h : is_line_distance_preference_profile a b ![psl3f201_PS3P201, psl3f201_PS3P210, psl3f201_PS3P012]) (σ : Equiv.Perm (Fin 3)) :
    probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P210, psl3f201_PS3P012] ≤ 3 * ∑ i, |a i - b (σ i)| := by
  have hX : ((psl3f201_psPhaseQ 3 ![psl3f201_PS3P201, psl3f201_PS3P210, psl3f201_PS3P012])^[3] (fun _ => 1, fun _ _ => 0)).2 = ![![(1/4 : ℚ), (1/4 : ℚ), (1/2 : ℚ)], ![(0 : ℚ), (1/2 : ℚ), (1/2 : ℚ)], ![(3/4 : ℚ), (1/4 : ℚ), (0 : ℚ)]] := by decide +kernel
  have e : probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P210, psl3f201_PS3P012] = (1/4 : ℝ) * |a 0 - b 0| + (1/4 : ℝ) * |a 0 - b 1| + (1/2 : ℝ) * |a 0 - b 2| + (1/2 : ℝ) * |a 1 - b 1| + (1/2 : ℝ) * |a 1 - b 2| + (3/4 : ℝ) * |a 2 - b 0| + (1/4 : ℝ) * |a 2 - b 1| := by
    unfold probabilistic_serial_line_cost
    simp only [psl3f201_psQ_cast, hX, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    push_cast; ring
  have p00 : |a 0 - b 2| ≤ |a 0 - b 0| := h 0 0 1 (by decide)
  have p01 : |a 0 - b 0| ≤ |a 0 - b 1| := h 0 1 2 (by decide)
  have p10 : |a 1 - b 2| ≤ |a 1 - b 1| := h 1 0 1 (by decide)
  have p11 : |a 1 - b 1| ≤ |a 1 - b 0| := h 1 1 2 (by decide)
  have p20 : |a 2 - b 0| ≤ |a 2 - b 1| := h 2 0 1 (by decide)
  have p21 : |a 2 - b 1| ≤ |a 2 - b 2| := h 2 1 2 (by decide)
  rw [e]
  rcases psl3f201_ps3_perm_cases σ with rfl | rfl | rfl | rfl | rfl | rfl
  · have hc : ∑ i, |a i - b (psl3f201_PS3P012 i)| = |a 0 - b 0| + |a 1 - b 1| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triC (a 0) (a 1) (b 1), psl3f201_triB (a 0) (a 1) (b 2), psl3f201_triC (a 0) (b 0) (b 1), psl3f201_triA (a 0) (b 0) (b 2), psl3f201_triA (a 2) (b 0) (b 1), psl3f201_triB (a 2) (b 0) (b 2), p00, p10, p20, p21, abs_nonneg (a 0 - b 0), abs_nonneg (a 1 - b 1), abs_nonneg (a 2 - b 2)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P021 i)| = |a 0 - b 0| + |a 1 - b 2| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triA (a 0) (a 1) (b 0), psl3f201_triC (a 0) (a 1) (b 2), psl3f201_triB (a 0) (a 1) (b 2), psl3f201_triB (a 0) (a 2) (b 1), psl3f201_triA (a 0) (a 2) (b 2), psl3f201_triC (a 0) (b 0) (b 1), psl3f201_triC (a 1) (a 2) (b 1), psl3f201_triB (a 1) (a 2) (b 2), psl3f201_triA (a 2) (b 0) (b 1), p00, p11, p20, abs_nonneg (a 0 - b 0), abs_nonneg (a 1 - b 2), abs_nonneg (a 2 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P102 i)| = |a 0 - b 1| + |a 1 - b 0| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [p00, p01, p10, p11, p20, p21, abs_nonneg (a 0 - b 1), abs_nonneg (a 1 - b 0), abs_nonneg (a 2 - b 2)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P120 i)| = |a 0 - b 1| + |a 1 - b 2| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triB (a 0) (a 2) (b 0), psl3f201_triA (a 0) (a 2) (b 1), psl3f201_triA (a 0) (b 1) (b 2), psl3f201_triB (a 1) (b 1) (b 2), psl3f201_triC (a 2) (b 0) (b 1), psl3f201_triA (a 2) (b 0) (b 1), p00, p01, abs_nonneg (a 1 - b 2), abs_nonneg (a 0 - b 1), abs_nonneg (a 2 - b 0)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P201 i)| = |a 0 - b 2| + |a 1 - b 0| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triC (a 0) (a 1) (b 0), psl3f201_triB (a 0) (a 1) (b 2), psl3f201_triB (a 0) (b 0) (b 2), psl3f201_triA (a 0) (b 0) (b 2), psl3f201_triB (a 0) (b 1) (b 2), psl3f201_triB (a 1) (a 2) (b 0), psl3f201_triC (a 1) (a 2) (b 1), psl3f201_triA (a 1) (a 2) (b 2), psl3f201_triA (a 2) (b 1) (b 2), p10, p11, p20, abs_nonneg (a 0 - b 2), abs_nonneg (a 1 - b 0), abs_nonneg (a 2 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P210 i)| = |a 0 - b 2| + |a 1 - b 1| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triB (a 0) (a 2) (b 0), psl3f201_triA (a 0) (a 2) (b 2), psl3f201_triB (a 0) (b 1) (b 2), psl3f201_triA (a 1) (b 1) (b 2), p01, p10, p21, abs_nonneg (a 0 - b 2), abs_nonneg (a 2 - b 0), abs_nonneg (a 1 - b 1)]

theorem psl3f201_ps3_case_201_210_021 (a b : Fin 3 → ℝ)
    (h : is_line_distance_preference_profile a b ![psl3f201_PS3P201, psl3f201_PS3P210, psl3f201_PS3P021]) (σ : Equiv.Perm (Fin 3)) :
    probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P210, psl3f201_PS3P021] ≤ 3 * ∑ i, |a i - b (σ i)| := by
  have hX : ((psl3f201_psPhaseQ 3 ![psl3f201_PS3P201, psl3f201_PS3P210, psl3f201_PS3P021])^[3] (fun _ => 1, fun _ _ => 0)).2 = ![![(1/4 : ℚ), (1/4 : ℚ), (1/2 : ℚ)], ![(0 : ℚ), (1/2 : ℚ), (1/2 : ℚ)], ![(3/4 : ℚ), (1/4 : ℚ), (0 : ℚ)]] := by decide +kernel
  have e : probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P210, psl3f201_PS3P021] = (1/4 : ℝ) * |a 0 - b 0| + (1/4 : ℝ) * |a 0 - b 1| + (1/2 : ℝ) * |a 0 - b 2| + (1/2 : ℝ) * |a 1 - b 1| + (1/2 : ℝ) * |a 1 - b 2| + (3/4 : ℝ) * |a 2 - b 0| + (1/4 : ℝ) * |a 2 - b 1| := by
    unfold probabilistic_serial_line_cost
    simp only [psl3f201_psQ_cast, hX, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    push_cast; ring
  have p00 : |a 0 - b 2| ≤ |a 0 - b 0| := h 0 0 1 (by decide)
  have p01 : |a 0 - b 0| ≤ |a 0 - b 1| := h 0 1 2 (by decide)
  have p10 : |a 1 - b 2| ≤ |a 1 - b 1| := h 1 0 1 (by decide)
  have p11 : |a 1 - b 1| ≤ |a 1 - b 0| := h 1 1 2 (by decide)
  have p20 : |a 2 - b 0| ≤ |a 2 - b 2| := h 2 0 1 (by decide)
  have p21 : |a 2 - b 2| ≤ |a 2 - b 1| := h 2 1 2 (by decide)
  rw [e]
  rcases psl3f201_ps3_perm_cases σ with rfl | rfl | rfl | rfl | rfl | rfl
  · have hc : ∑ i, |a i - b (psl3f201_PS3P012 i)| = |a 0 - b 0| + |a 1 - b 1| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triB (a 0) (b 1) (b 2), psl3f201_triA (a 1) (a 2) (b 1), psl3f201_triB (a 1) (a 2) (b 2), psl3f201_triA (a 2) (b 1) (b 2), p00, p10, p20, abs_nonneg (a 0 - b 0), abs_nonneg (a 2 - b 0), abs_nonneg (a 1 - b 1), abs_nonneg (a 2 - b 2)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P021 i)| = |a 0 - b 0| + |a 1 - b 2| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triA (a 0) (a 1) (b 0), psl3f201_triC (a 0) (a 1) (b 2), psl3f201_triB (a 0) (a 1) (b 2), psl3f201_triC (a 0) (b 0) (b 1), psl3f201_triC (a 1) (a 2) (b 1), psl3f201_triB (a 1) (a 2) (b 2), psl3f201_triA (a 2) (b 0) (b 1), p00, p11, p20, p21, abs_nonneg (a 0 - b 0), abs_nonneg (a 1 - b 2), abs_nonneg (a 2 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P102 i)| = |a 0 - b 1| + |a 1 - b 0| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triA (a 0) (b 1) (b 2), psl3f201_triA (a 1) (b 1) (b 2), psl3f201_triB (a 2) (b 1) (b 2), p00, p01, p10, p11, p20, abs_nonneg (a 2 - b 2), abs_nonneg (a 0 - b 1), abs_nonneg (a 1 - b 0)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P120 i)| = |a 0 - b 1| + |a 1 - b 2| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triB (a 0) (a 2) (b 0), psl3f201_triA (a 0) (a 2) (b 1), psl3f201_triA (a 0) (b 1) (b 2), psl3f201_triB (a 1) (b 1) (b 2), p00, p01, abs_nonneg (a 1 - b 2), abs_nonneg (a 2 - b 0), abs_nonneg (a 0 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P201 i)| = |a 0 - b 2| + |a 1 - b 0| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triB (a 0) (b 0) (b 2), psl3f201_triB (a 0) (b 1) (b 2), psl3f201_triA (a 1) (b 0) (b 2), psl3f201_triA (a 2) (b 1) (b 2), p10, p11, p20, p21, abs_nonneg (a 0 - b 2), abs_nonneg (a 1 - b 0), abs_nonneg (a 2 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P210 i)| = |a 0 - b 2| + |a 1 - b 1| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triA (a 0) (a 1) (b 0), psl3f201_triB (a 0) (a 1) (b 2), psl3f201_triB (a 0) (b 1) (b 2), psl3f201_triA (a 1) (b 0) (b 1), psl3f201_triA (a 1) (b 1) (b 2), psl3f201_triC (a 2) (b 0) (b 1), p01, p10, abs_nonneg (a 0 - b 2), abs_nonneg (a 2 - b 0), abs_nonneg (a 1 - b 1)]

theorem psl3f201_ps3_case_201_210_102 (a b : Fin 3 → ℝ)
    (h : is_line_distance_preference_profile a b ![psl3f201_PS3P201, psl3f201_PS3P210, psl3f201_PS3P102]) (σ : Equiv.Perm (Fin 3)) :
    probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P210, psl3f201_PS3P102] ≤ 3 * ∑ i, |a i - b (σ i)| := by
  have hX : ((psl3f201_psPhaseQ 3 ![psl3f201_PS3P201, psl3f201_PS3P210, psl3f201_PS3P102])^[3] (fun _ => 1, fun _ _ => 0)).2 = ![![(1/2 : ℚ), (0 : ℚ), (1/2 : ℚ)], ![(1/4 : ℚ), (1/4 : ℚ), (1/2 : ℚ)], ![(1/4 : ℚ), (3/4 : ℚ), (0 : ℚ)]] := by decide +kernel
  have e : probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P210, psl3f201_PS3P102] = (1/2 : ℝ) * |a 0 - b 0| + (1/2 : ℝ) * |a 0 - b 2| + (1/4 : ℝ) * |a 1 - b 0| + (1/4 : ℝ) * |a 1 - b 1| + (1/2 : ℝ) * |a 1 - b 2| + (1/4 : ℝ) * |a 2 - b 0| + (3/4 : ℝ) * |a 2 - b 1| := by
    unfold probabilistic_serial_line_cost
    simp only [psl3f201_psQ_cast, hX, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    push_cast; ring
  have p00 : |a 0 - b 2| ≤ |a 0 - b 0| := h 0 0 1 (by decide)
  have p01 : |a 0 - b 0| ≤ |a 0 - b 1| := h 0 1 2 (by decide)
  have p10 : |a 1 - b 2| ≤ |a 1 - b 1| := h 1 0 1 (by decide)
  have p11 : |a 1 - b 1| ≤ |a 1 - b 0| := h 1 1 2 (by decide)
  have p20 : |a 2 - b 1| ≤ |a 2 - b 0| := h 2 0 1 (by decide)
  have p21 : |a 2 - b 0| ≤ |a 2 - b 2| := h 2 1 2 (by decide)
  rw [e]
  rcases psl3f201_ps3_perm_cases σ with rfl | rfl | rfl | rfl | rfl | rfl
  · have hc : ∑ i, |a i - b (psl3f201_PS3P012 i)| = |a 0 - b 0| + |a 1 - b 1| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triA (a 0) (a 1) (b 0), psl3f201_triB (a 0) (a 1) (b 2), psl3f201_triB (a 1) (b 0) (b 2), psl3f201_triA (a 1) (b 1) (b 2), psl3f201_triA (a 2) (b 0) (b 2), psl3f201_triB (a 2) (b 1) (b 2), p00, p10, p20, p21, abs_nonneg (a 0 - b 0), abs_nonneg (a 1 - b 1), abs_nonneg (a 2 - b 2)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P021 i)| = |a 0 - b 0| + |a 1 - b 2| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triA (a 0) (b 0) (b 2), psl3f201_triB (a 1) (a 2) (b 1), psl3f201_triA (a 1) (a 2) (b 2), psl3f201_triB (a 1) (b 0) (b 2), p00, p11, p21, abs_nonneg (a 1 - b 2), abs_nonneg (a 2 - b 1), abs_nonneg (a 0 - b 0)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P102 i)| = |a 0 - b 1| + |a 1 - b 0| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [p00, p01, p10, p11, p20, p21, abs_nonneg (a 0 - b 1), abs_nonneg (a 1 - b 0), abs_nonneg (a 2 - b 2)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P120 i)| = |a 0 - b 1| + |a 1 - b 2| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triB (a 0) (a 2) (b 1), psl3f201_triA (a 0) (a 2) (b 2), psl3f201_triA (a 0) (b 1) (b 2), psl3f201_triB (a 1) (b 0) (b 2), psl3f201_triB (a 1) (b 1) (b 2), psl3f201_triA (a 2) (b 0) (b 2), p00, p01, p20, abs_nonneg (a 1 - b 2), abs_nonneg (a 2 - b 0), abs_nonneg (a 0 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P201 i)| = |a 0 - b 2| + |a 1 - b 0| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triB (a 0) (b 0) (b 2), psl3f201_triA (a 1) (a 2) (b 0), psl3f201_triB (a 1) (a 2) (b 1), psl3f201_triA (a 1) (b 0) (b 2), p10, p11, abs_nonneg (a 0 - b 2), abs_nonneg (a 2 - b 1), abs_nonneg (a 1 - b 0)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P210 i)| = |a 0 - b 2| + |a 1 - b 1| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triB (a 0) (b 1) (b 2), psl3f201_triC (a 1) (b 0) (b 1), psl3f201_triB (a 1) (b 0) (b 1), psl3f201_triA (a 1) (b 1) (b 2), psl3f201_triA (a 2) (b 0) (b 1), p01, p10, p20, abs_nonneg (a 0 - b 2), abs_nonneg (a 1 - b 1), abs_nonneg (a 2 - b 0)]

theorem psl3f201_ps3_case_201_210_120 (a b : Fin 3 → ℝ)
    (h : is_line_distance_preference_profile a b ![psl3f201_PS3P201, psl3f201_PS3P210, psl3f201_PS3P120]) (σ : Equiv.Perm (Fin 3)) :
    probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P210, psl3f201_PS3P120] ≤ 3 * ∑ i, |a i - b (σ i)| := by
  have hX : ((psl3f201_psPhaseQ 3 ![psl3f201_PS3P201, psl3f201_PS3P210, psl3f201_PS3P120])^[3] (fun _ => 1, fun _ _ => 0)).2 = ![![(1/2 : ℚ), (0 : ℚ), (1/2 : ℚ)], ![(1/4 : ℚ), (1/4 : ℚ), (1/2 : ℚ)], ![(1/4 : ℚ), (3/4 : ℚ), (0 : ℚ)]] := by decide +kernel
  have e : probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P210, psl3f201_PS3P120] = (1/2 : ℝ) * |a 0 - b 0| + (1/2 : ℝ) * |a 0 - b 2| + (1/4 : ℝ) * |a 1 - b 0| + (1/4 : ℝ) * |a 1 - b 1| + (1/2 : ℝ) * |a 1 - b 2| + (1/4 : ℝ) * |a 2 - b 0| + (3/4 : ℝ) * |a 2 - b 1| := by
    unfold probabilistic_serial_line_cost
    simp only [psl3f201_psQ_cast, hX, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    push_cast; ring
  have p00 : |a 0 - b 2| ≤ |a 0 - b 0| := h 0 0 1 (by decide)
  have p01 : |a 0 - b 0| ≤ |a 0 - b 1| := h 0 1 2 (by decide)
  have p10 : |a 1 - b 2| ≤ |a 1 - b 1| := h 1 0 1 (by decide)
  have p11 : |a 1 - b 1| ≤ |a 1 - b 0| := h 1 1 2 (by decide)
  have p20 : |a 2 - b 1| ≤ |a 2 - b 2| := h 2 0 1 (by decide)
  have p21 : |a 2 - b 2| ≤ |a 2 - b 0| := h 2 1 2 (by decide)
  rw [e]
  rcases psl3f201_ps3_perm_cases σ with rfl | rfl | rfl | rfl | rfl | rfl
  · have hc : ∑ i, |a i - b (psl3f201_PS3P012 i)| = |a 0 - b 0| + |a 1 - b 1| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triA (a 0) (a 2) (b 0), psl3f201_triB (a 0) (a 2) (b 2), psl3f201_triB (a 1) (b 0) (b 1), psl3f201_triA (a 2) (b 0) (b 1), psl3f201_triA (a 2) (b 1) (b 2), p00, p10, p20, abs_nonneg (a 1 - b 1), abs_nonneg (b 1 - b 2), abs_nonneg (a 0 - b 0), abs_nonneg (a 2 - b 2)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P021 i)| = |a 0 - b 0| + |a 1 - b 2| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triA (a 0) (b 0) (b 1), psl3f201_triA (a 0) (b 0) (b 2), psl3f201_triB (a 0) (b 1) (b 2), psl3f201_triC (a 1) (a 2) (b 1), psl3f201_triB (a 1) (a 2) (b 1), psl3f201_triA (a 1) (a 2) (b 2), psl3f201_triB (a 1) (b 0) (b 2), psl3f201_triB (a 2) (b 0) (b 1), psl3f201_triA (a 2) (b 1) (b 2), p00, p11, abs_nonneg (a 1 - b 2), abs_nonneg (a 0 - b 0), abs_nonneg (a 2 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P102 i)| = |a 0 - b 1| + |a 1 - b 0| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triA (a 0) (b 0) (b 1), psl3f201_triA (a 1) (b 0) (b 1), psl3f201_triB (a 2) (b 0) (b 1), p00, p01, p10, p11, p20, abs_nonneg (a 2 - b 2), abs_nonneg (a 0 - b 1), abs_nonneg (a 1 - b 0)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P120 i)| = |a 0 - b 1| + |a 1 - b 2| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triA (a 0) (b 0) (b 2), psl3f201_triC (a 1) (a 2) (b 1), psl3f201_triB (a 1) (a 2) (b 2), psl3f201_triB (a 1) (b 0) (b 2), p00, p01, p20, p21, abs_nonneg (a 1 - b 2), abs_nonneg (a 0 - b 1), abs_nonneg (a 2 - b 0)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P201 i)| = |a 0 - b 2| + |a 1 - b 0| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triB (a 0) (b 0) (b 2), psl3f201_triA (a 1) (b 0) (b 1), psl3f201_triA (a 1) (b 0) (b 2), psl3f201_triB (a 2) (b 0) (b 1), p10, p11, abs_nonneg (a 0 - b 2), abs_nonneg (a 2 - b 1), abs_nonneg (a 1 - b 0)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P210 i)| = |a 0 - b 2| + |a 1 - b 1| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triC (a 0) (a 1) (b 1), psl3f201_triB (a 0) (a 1) (b 2), psl3f201_triC (a 0) (a 2) (b 0), psl3f201_triB (a 0) (a 2) (b 2), psl3f201_triB (a 1) (b 0) (b 1), psl3f201_triA (a 2) (b 0) (b 1), p01, p10, p20, p21, abs_nonneg (a 0 - b 2), abs_nonneg (a 1 - b 1), abs_nonneg (a 2 - b 0)]

theorem psl3f201_ps3_case_201_210_201 (a b : Fin 3 → ℝ)
    (h : is_line_distance_preference_profile a b ![psl3f201_PS3P201, psl3f201_PS3P210, psl3f201_PS3P201]) (σ : Equiv.Perm (Fin 3)) :
    probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P210, psl3f201_PS3P201] ≤ 3 * ∑ i, |a i - b (σ i)| := by
  have hX : ((psl3f201_psPhaseQ 3 ![psl3f201_PS3P201, psl3f201_PS3P210, psl3f201_PS3P201])^[3] (fun _ => 1, fun _ _ => 0)).2 = ![![(1/2 : ℚ), (1/6 : ℚ), (1/3 : ℚ)], ![(0 : ℚ), (2/3 : ℚ), (1/3 : ℚ)], ![(1/2 : ℚ), (1/6 : ℚ), (1/3 : ℚ)]] := by decide +kernel
  have e : probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P210, psl3f201_PS3P201] = (1/2 : ℝ) * |a 0 - b 0| + (1/6 : ℝ) * |a 0 - b 1| + (1/3 : ℝ) * |a 0 - b 2| + (2/3 : ℝ) * |a 1 - b 1| + (1/3 : ℝ) * |a 1 - b 2| + (1/2 : ℝ) * |a 2 - b 0| + (1/6 : ℝ) * |a 2 - b 1| + (1/3 : ℝ) * |a 2 - b 2| := by
    unfold probabilistic_serial_line_cost
    simp only [psl3f201_psQ_cast, hX, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    push_cast; ring
  have p00 : |a 0 - b 2| ≤ |a 0 - b 0| := h 0 0 1 (by decide)
  have p01 : |a 0 - b 0| ≤ |a 0 - b 1| := h 0 1 2 (by decide)
  have p10 : |a 1 - b 2| ≤ |a 1 - b 1| := h 1 0 1 (by decide)
  have p11 : |a 1 - b 1| ≤ |a 1 - b 0| := h 1 1 2 (by decide)
  have p20 : |a 2 - b 2| ≤ |a 2 - b 0| := h 2 0 1 (by decide)
  have p21 : |a 2 - b 0| ≤ |a 2 - b 1| := h 2 1 2 (by decide)
  rw [e]
  rcases psl3f201_ps3_perm_cases σ with rfl | rfl | rfl | rfl | rfl | rfl
  · have hc : ∑ i, |a i - b (psl3f201_PS3P012 i)| = |a 0 - b 0| + |a 1 - b 1| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triA (a 0) (a 2) (b 0), psl3f201_triC (a 0) (a 2) (b 1), psl3f201_triB (a 0) (a 2) (b 2), psl3f201_triA (a 1) (a 2) (b 1), psl3f201_triB (a 1) (a 2) (b 2), p00, p10, p21, abs_nonneg (a 2 - b 2), abs_nonneg (a 0 - b 0), abs_nonneg (a 1 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P021 i)| = |a 0 - b 0| + |a 1 - b 2| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triC (a 0) (b 0) (b 1), psl3f201_triA (a 0) (b 0) (b 2), psl3f201_triB (a 1) (b 0) (b 2), psl3f201_triA (a 2) (b 0) (b 1), psl3f201_triA (a 2) (b 0) (b 2), p00, p11, p20, p21, abs_nonneg (a 1 - b 2), abs_nonneg (a 0 - b 0), abs_nonneg (a 2 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P102 i)| = |a 0 - b 1| + |a 1 - b 0| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triA (a 0) (a 2) (b 1), psl3f201_triB (a 0) (a 2) (b 2), psl3f201_triA (a 1) (a 2) (b 0), psl3f201_triB (a 1) (a 2) (b 2), p00, p01, p10, p11, p21, abs_nonneg (a 2 - b 2), abs_nonneg (a 0 - b 1), abs_nonneg (a 1 - b 0)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P120 i)| = |a 0 - b 1| + |a 1 - b 2| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triA (a 0) (a 1) (b 1), psl3f201_triB (a 0) (a 1) (b 2), psl3f201_triB (a 0) (a 2) (b 0), psl3f201_triA (a 0) (a 2) (b 1), psl3f201_triC (a 1) (a 2) (b 0), psl3f201_triB (a 1) (a 2) (b 2), p00, p01, p11, p20, abs_nonneg (a 1 - b 2), abs_nonneg (a 0 - b 1), abs_nonneg (a 2 - b 0)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P201 i)| = |a 0 - b 2| + |a 1 - b 0| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triC (a 0) (a 1) (b 0), psl3f201_triB (a 0) (a 1) (b 2), psl3f201_triB (a 0) (b 1) (b 2), psl3f201_triA (a 2) (b 1) (b 2), p01, p10, p11, p20, p21, abs_nonneg (a 0 - b 2), abs_nonneg (a 1 - b 0), abs_nonneg (a 2 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P210 i)| = |a 0 - b 2| + |a 1 - b 1| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triC (a 0) (a 1) (b 1), psl3f201_triB (a 0) (a 1) (b 2), psl3f201_triB (a 0) (b 0) (b 2), psl3f201_triA (a 1) (a 2) (b 1), psl3f201_triB (a 1) (a 2) (b 2), psl3f201_triA (a 2) (b 0) (b 2), p01, p10, p20, abs_nonneg (a 0 - b 2), abs_nonneg (a 1 - b 1), abs_nonneg (a 2 - b 0)]

theorem psl3f201_ps3_case_201_210_210 (a b : Fin 3 → ℝ)
    (h : is_line_distance_preference_profile a b ![psl3f201_PS3P201, psl3f201_PS3P210, psl3f201_PS3P210]) (σ : Equiv.Perm (Fin 3)) :
    probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P210, psl3f201_PS3P210] ≤ 3 * ∑ i, |a i - b (σ i)| := by
  have hX : ((psl3f201_psPhaseQ 3 ![psl3f201_PS3P201, psl3f201_PS3P210, psl3f201_PS3P210])^[3] (fun _ => 1, fun _ _ => 0)).2 = ![![(2/3 : ℚ), (0 : ℚ), (1/3 : ℚ)], ![(1/6 : ℚ), (1/2 : ℚ), (1/3 : ℚ)], ![(1/6 : ℚ), (1/2 : ℚ), (1/3 : ℚ)]] := by decide +kernel
  have e : probabilistic_serial_line_cost a b ![psl3f201_PS3P201, psl3f201_PS3P210, psl3f201_PS3P210] = (2/3 : ℝ) * |a 0 - b 0| + (1/3 : ℝ) * |a 0 - b 2| + (1/6 : ℝ) * |a 1 - b 0| + (1/2 : ℝ) * |a 1 - b 1| + (1/3 : ℝ) * |a 1 - b 2| + (1/6 : ℝ) * |a 2 - b 0| + (1/2 : ℝ) * |a 2 - b 1| + (1/3 : ℝ) * |a 2 - b 2| := by
    unfold probabilistic_serial_line_cost
    simp only [psl3f201_psQ_cast, hX, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
    push_cast; ring
  have p00 : |a 0 - b 2| ≤ |a 0 - b 0| := h 0 0 1 (by decide)
  have p01 : |a 0 - b 0| ≤ |a 0 - b 1| := h 0 1 2 (by decide)
  have p10 : |a 1 - b 2| ≤ |a 1 - b 1| := h 1 0 1 (by decide)
  have p11 : |a 1 - b 1| ≤ |a 1 - b 0| := h 1 1 2 (by decide)
  have p20 : |a 2 - b 2| ≤ |a 2 - b 1| := h 2 0 1 (by decide)
  have p21 : |a 2 - b 1| ≤ |a 2 - b 0| := h 2 1 2 (by decide)
  rw [e]
  rcases psl3f201_ps3_perm_cases σ with rfl | rfl | rfl | rfl | rfl | rfl
  · have hc : ∑ i, |a i - b (psl3f201_PS3P012 i)| = |a 0 - b 0| + |a 1 - b 1| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triA (a 0) (a 2) (b 0), psl3f201_triB (a 0) (a 2) (b 2), psl3f201_triA (a 1) (a 2) (b 1), psl3f201_triB (a 1) (a 2) (b 2), psl3f201_triB (a 1) (b 0) (b 2), psl3f201_triA (a 2) (b 0) (b 2), p00, p10, p21, abs_nonneg (a 2 - b 2), abs_nonneg (a 0 - b 0), abs_nonneg (a 1 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P021 i)| = |a 0 - b 0| + |a 1 - b 2| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triA (a 0) (a 2) (b 0), psl3f201_triB (a 0) (a 2) (b 2), psl3f201_triA (a 0) (b 0) (b 2), psl3f201_triC (a 1) (a 2) (b 1), psl3f201_triB (a 1) (a 2) (b 2), psl3f201_triB (a 1) (b 0) (b 2), p00, p11, p20, abs_nonneg (a 1 - b 2), abs_nonneg (a 0 - b 0), abs_nonneg (a 2 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P102 i)| = |a 0 - b 1| + |a 1 - b 0| + |a 2 - b 2| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triA (a 0) (a 2) (b 1), psl3f201_triB (a 0) (a 2) (b 2), psl3f201_triA (a 1) (a 2) (b 0), psl3f201_triB (a 1) (a 2) (b 2), psl3f201_triA (a 1) (b 1) (b 2), psl3f201_triB (a 2) (b 1) (b 2), p00, p01, p10, p11, abs_nonneg (a 2 - b 2), abs_nonneg (a 0 - b 1), abs_nonneg (a 1 - b 0)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P120 i)| = |a 0 - b 1| + |a 1 - b 2| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triA (a 0) (a 1) (b 1), psl3f201_triB (a 0) (a 1) (b 2), psl3f201_triC (a 1) (a 2) (b 0), psl3f201_triB (a 1) (a 2) (b 2), p00, p01, p11, p20, p21, abs_nonneg (a 1 - b 2), abs_nonneg (a 0 - b 1), abs_nonneg (a 2 - b 0)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P201 i)| = |a 0 - b 2| + |a 1 - b 0| + |a 2 - b 1| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triC (a 0) (a 1) (b 0), psl3f201_triB (a 0) (a 1) (b 2), psl3f201_triB (a 0) (b 1) (b 2), psl3f201_triA (a 1) (a 2) (b 0), psl3f201_triB (a 1) (a 2) (b 1), psl3f201_triA (a 2) (b 1) (b 2), p01, p10, p11, p20, abs_nonneg (a 0 - b 2), abs_nonneg (a 1 - b 0), abs_nonneg (a 2 - b 1)]
  · have hc : ∑ i, |a i - b (psl3f201_PS3P210 i)| = |a 0 - b 2| + |a 1 - b 1| + |a 2 - b 0| := by rw [Fin.sum_univ_three]; rfl
    rw [hc]; linarith only [psl3f201_triC (a 0) (a 2) (b 0), psl3f201_triB (a 0) (a 2) (b 2), psl3f201_triB (a 0) (b 1) (b 2), psl3f201_triC (a 1) (a 2) (b 0), psl3f201_triB (a 1) (a 2) (b 1), psl3f201_triA (a 1) (b 1) (b 2), p01, p10, p20, p21, abs_nonneg (a 0 - b 2), abs_nonneg (a 1 - b 1), abs_nonneg (a 2 - b 0)]

theorem probabilistic_serial_line_three_agents_le_of_first_choices_20 (a b : Fin 3 → ℝ) (pref : Fin 3 → Equiv.Perm (Fin 3))
    (h : is_line_distance_preference_profile a b pref) (h0 : pref 0 0 = 2) (h1 : pref 0 1 = 0)
    (σ : Equiv.Perm (Fin 3)) :
    probabilistic_serial_line_cost a b pref ≤ 3 * ∑ i, |a i - b (σ i)| := by
  have h2 : pref 0 2 = 1 := by
    have u : pref 0 2 ≠ pref 0 0 := (pref 0).injective.ne (by decide)
    have v : pref 0 2 ≠ pref 0 1 := (pref 0).injective.ne (by decide)
    rw [h0] at u; rw [h1] at v; omega
  have e0 : pref 0 = psl3f201_PS3P201 := Equiv.ext (fun k => by fin_cases k; exacts [h0, h1, h2])
  rcases psl3f201_ps3_perm_cases (pref 1) with e1 | e1 | e1 | e1 | e1 | e1 <;>
  rcases psl3f201_ps3_perm_cases (pref 2) with e2 | e2 | e2 | e2 | e2 | e2
  · have hp : pref = ![pref 0, pref 1, pref 2] := by funext i; fin_cases i <;> rfl
    rw [e0, e1, e2] at hp; subst hp; exact psl3f201_ps3_case_201_012_012 a b h σ
  · have hp : pref = ![pref 0, pref 1, pref 2] := by funext i; fin_cases i <;> rfl
    rw [e0, e1, e2] at hp; subst hp; exact psl3f201_ps3_case_201_012_021 a b h σ
  · have hp : pref = ![pref 0, pref 1, pref 2] := by funext i; fin_cases i <;> rfl
    rw [e0, e1, e2] at hp; subst hp; exact psl3f201_ps3_case_201_012_102 a b h σ
  · have hp : pref = ![pref 0, pref 1, pref 2] := by funext i; fin_cases i <;> rfl
    rw [e0, e1, e2] at hp; subst hp; exact psl3f201_ps3_case_201_012_120 a b h σ
  · have hp : pref = ![pref 0, pref 1, pref 2] := by funext i; fin_cases i <;> rfl
    rw [e0, e1, e2] at hp; subst hp; exact psl3f201_ps3_case_201_012_201 a b h σ
  · have hp : pref = ![pref 0, pref 1, pref 2] := by funext i; fin_cases i <;> rfl
    rw [e0, e1, e2] at hp; subst hp; exact psl3f201_ps3_case_201_012_210 a b h σ
  · have hp : pref = ![pref 0, pref 1, pref 2] := by funext i; fin_cases i <;> rfl
    rw [e0, e1, e2] at hp; subst hp; exact psl3f201_ps3_case_201_021_012 a b h σ
  · have hp : pref = ![pref 0, pref 1, pref 2] := by funext i; fin_cases i <;> rfl
    rw [e0, e1, e2] at hp; subst hp; exact psl3f201_ps3_case_201_021_021 a b h σ
  · have hp : pref = ![pref 0, pref 1, pref 2] := by funext i; fin_cases i <;> rfl
    rw [e0, e1, e2] at hp; subst hp; exact psl3f201_ps3_case_201_021_102 a b h σ
  · have hp : pref = ![pref 0, pref 1, pref 2] := by funext i; fin_cases i <;> rfl
    rw [e0, e1, e2] at hp; subst hp; exact psl3f201_ps3_case_201_021_120 a b h σ
  · have hp : pref = ![pref 0, pref 1, pref 2] := by funext i; fin_cases i <;> rfl
    rw [e0, e1, e2] at hp; subst hp; exact psl3f201_ps3_case_201_021_201 a b h σ
  · have hp : pref = ![pref 0, pref 1, pref 2] := by funext i; fin_cases i <;> rfl
    rw [e0, e1, e2] at hp; subst hp; exact psl3f201_ps3_case_201_021_210 a b h σ
  · have hp : pref = ![pref 0, pref 1, pref 2] := by funext i; fin_cases i <;> rfl
    rw [e0, e1, e2] at hp; subst hp; exact psl3f201_ps3_case_201_102_012 a b h σ
  · have hp : pref = ![pref 0, pref 1, pref 2] := by funext i; fin_cases i <;> rfl
    rw [e0, e1, e2] at hp; subst hp; exact psl3f201_ps3_case_201_102_021 a b h σ
  · have hp : pref = ![pref 0, pref 1, pref 2] := by funext i; fin_cases i <;> rfl
    rw [e0, e1, e2] at hp; subst hp; exact psl3f201_ps3_case_201_102_102 a b h σ
  · have hp : pref = ![pref 0, pref 1, pref 2] := by funext i; fin_cases i <;> rfl
    rw [e0, e1, e2] at hp; subst hp; exact psl3f201_ps3_case_201_102_120 a b h σ
  · have hp : pref = ![pref 0, pref 1, pref 2] := by funext i; fin_cases i <;> rfl
    rw [e0, e1, e2] at hp; subst hp; exact psl3f201_ps3_case_201_102_201 a b h σ
  · have hp : pref = ![pref 0, pref 1, pref 2] := by funext i; fin_cases i <;> rfl
    rw [e0, e1, e2] at hp; subst hp; exact psl3f201_ps3_case_201_102_210 a b h σ
  · have hp : pref = ![pref 0, pref 1, pref 2] := by funext i; fin_cases i <;> rfl
    rw [e0, e1, e2] at hp; subst hp; exact psl3f201_ps3_case_201_120_012 a b h σ
  · have hp : pref = ![pref 0, pref 1, pref 2] := by funext i; fin_cases i <;> rfl
    rw [e0, e1, e2] at hp; subst hp; exact psl3f201_ps3_case_201_120_021 a b h σ
  · have hp : pref = ![pref 0, pref 1, pref 2] := by funext i; fin_cases i <;> rfl
    rw [e0, e1, e2] at hp; subst hp; exact psl3f201_ps3_case_201_120_102 a b h σ
  · have hp : pref = ![pref 0, pref 1, pref 2] := by funext i; fin_cases i <;> rfl
    rw [e0, e1, e2] at hp; subst hp; exact psl3f201_ps3_case_201_120_120 a b h σ
  · have hp : pref = ![pref 0, pref 1, pref 2] := by funext i; fin_cases i <;> rfl
    rw [e0, e1, e2] at hp; subst hp; exact psl3f201_ps3_case_201_120_201 a b h σ
  · have hp : pref = ![pref 0, pref 1, pref 2] := by funext i; fin_cases i <;> rfl
    rw [e0, e1, e2] at hp; subst hp; exact psl3f201_ps3_case_201_120_210 a b h σ
  · have hp : pref = ![pref 0, pref 1, pref 2] := by funext i; fin_cases i <;> rfl
    rw [e0, e1, e2] at hp; subst hp; exact psl3f201_ps3_case_201_201_012 a b h σ
  · have hp : pref = ![pref 0, pref 1, pref 2] := by funext i; fin_cases i <;> rfl
    rw [e0, e1, e2] at hp; subst hp; exact psl3f201_ps3_case_201_201_021 a b h σ
  · have hp : pref = ![pref 0, pref 1, pref 2] := by funext i; fin_cases i <;> rfl
    rw [e0, e1, e2] at hp; subst hp; exact psl3f201_ps3_case_201_201_102 a b h σ
  · have hp : pref = ![pref 0, pref 1, pref 2] := by funext i; fin_cases i <;> rfl
    rw [e0, e1, e2] at hp; subst hp; exact psl3f201_ps3_case_201_201_120 a b h σ
  · have hp : pref = ![pref 0, pref 1, pref 2] := by funext i; fin_cases i <;> rfl
    rw [e0, e1, e2] at hp; subst hp; exact psl3f201_ps3_case_201_201_201 a b h σ
  · have hp : pref = ![pref 0, pref 1, pref 2] := by funext i; fin_cases i <;> rfl
    rw [e0, e1, e2] at hp; subst hp; exact psl3f201_ps3_case_201_201_210 a b h σ
  · have hp : pref = ![pref 0, pref 1, pref 2] := by funext i; fin_cases i <;> rfl
    rw [e0, e1, e2] at hp; subst hp; exact psl3f201_ps3_case_201_210_012 a b h σ
  · have hp : pref = ![pref 0, pref 1, pref 2] := by funext i; fin_cases i <;> rfl
    rw [e0, e1, e2] at hp; subst hp; exact psl3f201_ps3_case_201_210_021 a b h σ
  · have hp : pref = ![pref 0, pref 1, pref 2] := by funext i; fin_cases i <;> rfl
    rw [e0, e1, e2] at hp; subst hp; exact psl3f201_ps3_case_201_210_102 a b h σ
  · have hp : pref = ![pref 0, pref 1, pref 2] := by funext i; fin_cases i <;> rfl
    rw [e0, e1, e2] at hp; subst hp; exact psl3f201_ps3_case_201_210_120 a b h σ
  · have hp : pref = ![pref 0, pref 1, pref 2] := by funext i; fin_cases i <;> rfl
    rw [e0, e1, e2] at hp; subst hp; exact psl3f201_ps3_case_201_210_201 a b h σ
  · have hp : pref = ![pref 0, pref 1, pref 2] := by funext i; fin_cases i <;> rfl
    rw [e0, e1, e2] at hp; subst hp; exact psl3f201_ps3_case_201_210_210 a b h σ
