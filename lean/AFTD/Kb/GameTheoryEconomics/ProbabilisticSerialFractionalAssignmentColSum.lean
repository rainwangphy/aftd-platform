import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ProbabilisticSerialFractionalAssignment
import AFTD.Kb.GameTheoryEconomics.ProbabilisticSerialPhaseState
import AFTD.Kb.GameTheoryEconomics.ProbabilisticSerialPhase
import AFTD.Kb.GameTheoryEconomics.ProbabilisticSerialFractionalAssignmentRowSum

/-!
# probabilistic_serial_fractional_assignment_col_sum

Topic: social_choice   Node: b437e3a3e707

Provenance: helper lemma. step towards probabilistic_serial_line_metric_sharp_linear_distortion

Every item is fully eaten under probabilistic serial: the column sums of the probabilistic serial assignment are 1.
-/

private noncomputable abbrev probabilistic_serial_fractional_assignment_col_sum_eats
    (n : ℕ) (pref : Fin n → Equiv.Perm (Fin n))
    (s : (Fin n → ℝ) × (Fin n → Fin n → ℝ)) (i j : Fin n) : Prop :=
  0 < s.1 j ∧ ∀ (j' : Fin n), 0 < s.1 j' → (pref i).symm j ≤ (pref i).symm j'

private noncomputable abbrev probabilistic_serial_fractional_assignment_col_sum_cnt
    (n : ℕ) (pref : Fin n → Equiv.Perm (Fin n))
    (s : (Fin n → ℝ) × (Fin n → Fin n → ℝ)) (j : Fin n) : ℕ :=
  (Finset.univ.filter
    (fun i => probabilistic_serial_fractional_assignment_col_sum_eats n pref s i j)).card

private noncomputable abbrev probabilistic_serial_fractional_assignment_col_sum_S
    (n : ℕ) (pref : Fin n → Equiv.Perm (Fin n))
    (s : (Fin n → ℝ) × (Fin n → Fin n → ℝ)) : Finset (Fin n) :=
  Finset.univ.filter
    (fun j => 0 < probabilistic_serial_fractional_assignment_col_sum_cnt n pref s j)

private noncomputable abbrev probabilistic_serial_fractional_assignment_col_sum_T
    (n : ℕ) (pref : Fin n → Equiv.Perm (Fin n))
    (s : (Fin n → ℝ) × (Fin n → Fin n → ℝ)) : ℝ :=
  if h : (probabilistic_serial_fractional_assignment_col_sum_S n pref s).Nonempty then
    (probabilistic_serial_fractional_assignment_col_sum_S n pref s).inf' h
      (fun j => s.1 j / (probabilistic_serial_fractional_assignment_col_sum_cnt n pref s j : ℝ))
  else 0

private theorem probabilistic_serial_fractional_assignment_col_sum_phase_eq
    (n : ℕ) (pref : Fin n → Equiv.Perm (Fin n))
    (s : (Fin n → ℝ) × (Fin n → Fin n → ℝ)) :
    probabilistic_serial_phase n pref s =
      (fun j => s.1 j - probabilistic_serial_fractional_assignment_col_sum_T n pref s *
          (probabilistic_serial_fractional_assignment_col_sum_cnt n pref s j : ℝ),
       fun i j => s.2 i j +
          if probabilistic_serial_fractional_assignment_col_sum_eats n pref s i j then
            probabilistic_serial_fractional_assignment_col_sum_T n pref s else 0) := rfl

private theorem probabilistic_serial_fractional_assignment_col_sum_state_succ
    (n : ℕ) (pref : Fin n → Equiv.Perm (Fin n)) (k : ℕ) :
    probabilistic_serial_phase_state n pref (k + 1) =
      probabilistic_serial_phase n pref (probabilistic_serial_phase_state n pref k) := by
  show (probabilistic_serial_phase n pref)^[k+1] (fun x => 1, fun x x_1 => 0) =
      probabilistic_serial_phase n pref
        ((probabilistic_serial_phase n pref)^[k] (fun x => 1, fun x x_1 => 0))
  rw [Function.iterate_succ_apply']

private theorem probabilistic_serial_fractional_assignment_col_sum_T_mul_le
    (n : ℕ) (pref : Fin n → Equiv.Perm (Fin n))
    (s : (Fin n → ℝ) × (Fin n → Fin n → ℝ)) (hpos : ∀ j, 0 ≤ s.1 j) (j : Fin n) :
    probabilistic_serial_fractional_assignment_col_sum_T n pref s *
      (probabilistic_serial_fractional_assignment_col_sum_cnt n pref s j : ℝ) ≤ s.1 j := by
  by_cases hc : probabilistic_serial_fractional_assignment_col_sum_cnt n pref s j = 0
  · rw [hc]; push_cast; rw [mul_zero]; exact hpos j
  · have hcpos : 0 < probabilistic_serial_fractional_assignment_col_sum_cnt n pref s j :=
      Nat.pos_of_ne_zero hc
    have hmem : j ∈ probabilistic_serial_fractional_assignment_col_sum_S n pref s := by
      rw [probabilistic_serial_fractional_assignment_col_sum_S, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, hcpos⟩
    have hcastpos : (0:ℝ) <
        (probabilistic_serial_fractional_assignment_col_sum_cnt n pref s j : ℝ) := by
      exact_mod_cast hcpos
    have hS : (probabilistic_serial_fractional_assignment_col_sum_S n pref s).Nonempty :=
      ⟨j, hmem⟩
    have hT : probabilistic_serial_fractional_assignment_col_sum_T n pref s =
        (probabilistic_serial_fractional_assignment_col_sum_S n pref s).inf' hS
          (fun j => s.1 j /
            (probabilistic_serial_fractional_assignment_col_sum_cnt n pref s j : ℝ)) := by
      simp only [probabilistic_serial_fractional_assignment_col_sum_T]; exact dif_pos hS
    have hle : (probabilistic_serial_fractional_assignment_col_sum_S n pref s).inf' hS
          (fun j => s.1 j /
            (probabilistic_serial_fractional_assignment_col_sum_cnt n pref s j : ℝ)) ≤
        s.1 j / (probabilistic_serial_fractional_assignment_col_sum_cnt n pref s j : ℝ) :=
      Finset.inf'_le _ hmem
    rw [hT]
    calc (probabilistic_serial_fractional_assignment_col_sum_S n pref s).inf' hS
            (fun j => s.1 j /
              (probabilistic_serial_fractional_assignment_col_sum_cnt n pref s j : ℝ)) *
          (probabilistic_serial_fractional_assignment_col_sum_cnt n pref s j : ℝ)
        ≤ (s.1 j / (probabilistic_serial_fractional_assignment_col_sum_cnt n pref s j : ℝ)) *
          (probabilistic_serial_fractional_assignment_col_sum_cnt n pref s j : ℝ) :=
          mul_le_mul_of_nonneg_right hle (le_of_lt hcastpos)
      _ = s.1 j := div_mul_cancel₀ (s.1 j) (ne_of_gt hcastpos)

private noncomputable abbrev probabilistic_serial_fractional_assignment_col_sum_cap
    (n : ℕ) (pref : Fin n → Equiv.Perm (Fin n)) (k : ℕ) : Fin n → ℝ :=
  (probabilistic_serial_phase_state n pref k).1

private noncomputable abbrev probabilistic_serial_fractional_assignment_col_sum_col
    (n : ℕ) (pref : Fin n → Equiv.Perm (Fin n)) (k : ℕ) (j : Fin n) : ℝ :=
  ∑ i, (probabilistic_serial_phase_state n pref k).2 i j

private theorem probabilistic_serial_fractional_assignment_col_sum_cap_nonneg
    (n : ℕ) (pref : Fin n → Equiv.Perm (Fin n)) (k : ℕ) :
    ∀ j, 0 ≤ probabilistic_serial_fractional_assignment_col_sum_cap n pref k j := by
  induction k with
  | zero => intro j; simp [probabilistic_serial_fractional_assignment_col_sum_cap,
      probabilistic_serial_phase_state]
  | succ k ih =>
      intro j
      have hcap : probabilistic_serial_fractional_assignment_col_sum_cap n pref (k+1) j =
          probabilistic_serial_fractional_assignment_col_sum_cap n pref k j -
            probabilistic_serial_fractional_assignment_col_sum_T n pref
              (probabilistic_serial_phase_state n pref k) *
            (probabilistic_serial_fractional_assignment_col_sum_cnt n pref
              (probabilistic_serial_phase_state n pref k) j : ℝ) := by
        simp only [probabilistic_serial_fractional_assignment_col_sum_cap,
          probabilistic_serial_fractional_assignment_col_sum_state_succ,
          probabilistic_serial_fractional_assignment_col_sum_phase_eq]
      have hle := probabilistic_serial_fractional_assignment_col_sum_T_mul_le n pref
        (probabilistic_serial_phase_state n pref k) (fun j => ih j) j
      rw [hcap]
      linarith

private theorem probabilistic_serial_fractional_assignment_col_sum_col_phase
    (n : ℕ) (pref : Fin n → Equiv.Perm (Fin n))
    (s : (Fin n → ℝ) × (Fin n → Fin n → ℝ)) (j : Fin n) :
    (∑ i, (probabilistic_serial_phase n pref s).2 i j) =
      (∑ i, s.2 i j) +
        probabilistic_serial_fractional_assignment_col_sum_T n pref s *
          (probabilistic_serial_fractional_assignment_col_sum_cnt n pref s j : ℝ) := by
  rw [probabilistic_serial_fractional_assignment_col_sum_phase_eq]
  simp only [Finset.sum_add_distrib]
  congr 1
  calc (∑ x, if probabilistic_serial_fractional_assignment_col_sum_eats n pref s x j
        then probabilistic_serial_fractional_assignment_col_sum_T n pref s else (0:ℝ))
      = ∑ x, probabilistic_serial_fractional_assignment_col_sum_T n pref s *
          (if probabilistic_serial_fractional_assignment_col_sum_eats n pref s x j
            then (1:ℝ) else 0) := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : probabilistic_serial_fractional_assignment_col_sum_eats n pref s x j
        · simp [hx]
        · simp [hx]
    _ = probabilistic_serial_fractional_assignment_col_sum_T n pref s *
          (∑ x, (if probabilistic_serial_fractional_assignment_col_sum_eats n pref s x j
            then (1:ℝ) else 0)) := by
        rw [Finset.mul_sum]
    _ = probabilistic_serial_fractional_assignment_col_sum_T n pref s *
          (probabilistic_serial_fractional_assignment_col_sum_cnt n pref s j : ℝ) := by
        congr 1
        exact Finset.sum_boole
          (fun i => probabilistic_serial_fractional_assignment_col_sum_eats n pref s i j)
          Finset.univ

private theorem probabilistic_serial_fractional_assignment_col_sum_col_form
    (n : ℕ) (pref : Fin n → Equiv.Perm (Fin n)) (k : ℕ) (j : Fin n) :
    probabilistic_serial_fractional_assignment_col_sum_cap n pref k j +
      probabilistic_serial_fractional_assignment_col_sum_col n pref k j = 1 := by
  induction k with
  | zero => simp [probabilistic_serial_fractional_assignment_col_sum_cap,
      probabilistic_serial_fractional_assignment_col_sum_col, probabilistic_serial_phase_state]
  | succ k ih =>
      have hcap : probabilistic_serial_fractional_assignment_col_sum_cap n pref (k+1) j =
          probabilistic_serial_fractional_assignment_col_sum_cap n pref k j -
            probabilistic_serial_fractional_assignment_col_sum_T n pref
              (probabilistic_serial_phase_state n pref k) *
            (probabilistic_serial_fractional_assignment_col_sum_cnt n pref
              (probabilistic_serial_phase_state n pref k) j : ℝ) := by
        simp only [probabilistic_serial_fractional_assignment_col_sum_cap,
          probabilistic_serial_fractional_assignment_col_sum_state_succ,
          probabilistic_serial_fractional_assignment_col_sum_phase_eq]
      have hcol : probabilistic_serial_fractional_assignment_col_sum_col n pref (k+1) j =
          probabilistic_serial_fractional_assignment_col_sum_col n pref k j +
            probabilistic_serial_fractional_assignment_col_sum_T n pref
              (probabilistic_serial_phase_state n pref k) *
            (probabilistic_serial_fractional_assignment_col_sum_cnt n pref
              (probabilistic_serial_phase_state n pref k) j : ℝ) := by
        simp only [probabilistic_serial_fractional_assignment_col_sum_col,
          probabilistic_serial_fractional_assignment_col_sum_state_succ]
        exact probabilistic_serial_fractional_assignment_col_sum_col_phase n pref
          (probabilistic_serial_phase_state n pref k) j
      rw [hcap, hcol]
      linarith [ih]

/-- Every item is fully eaten under probabilistic serial: the column sums of the PS assignment equal 1. -/
theorem probabilistic_serial_fractional_assignment_col_sum (n : ℕ) (hn : 1 ≤ n) (pref : Fin n → Equiv.Perm (Fin n)) (j : Fin n) : ∑ i, probabilistic_serial_fractional_assignment n pref i j = 1 := by
  let c : Fin n → ℝ := fun j => ∑ i, probabilistic_serial_fractional_assignment n pref i j
  have hle : ∀ j, c j ≤ 1 := by
    intro j
    have hinv := probabilistic_serial_fractional_assignment_col_sum_col_form n pref n j
    have hnn := probabilistic_serial_fractional_assignment_col_sum_cap_nonneg n pref n j
    have e : probabilistic_serial_fractional_assignment_col_sum_col n pref n j = c j := rfl
    rw [e] at hinv
    linarith
  have hrow : ∀ i, ∑ j, probabilistic_serial_fractional_assignment n pref i j = 1 :=
    fun i => probabilistic_serial_fractional_assignment_row_sum n hn pref i
  have htotal : ∑ j, c j = (n:ℝ) := by
    simp only [c]
    rw [Finset.sum_comm]
    simp [hrow]
  have hd : ∑ j, (1 - c j) = 0 := by
    rw [Finset.sum_sub_distrib, htotal]
    simp
  have hnn : ∀ j ∈ (Finset.univ : Finset (Fin n)), 0 ≤ 1 - c j := by
    intro j _; linarith [hle j]
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ) hnn).mp hd
  have hj := hz j (Finset.mem_univ j)
  show c j = 1
  linarith
