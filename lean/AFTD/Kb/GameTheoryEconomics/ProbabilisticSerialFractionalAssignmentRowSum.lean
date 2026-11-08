import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ProbabilisticSerialFractionalAssignment
import AFTD.Kb.GameTheoryEconomics.ProbabilisticSerialPhase
import AFTD.Kb.GameTheoryEconomics.ProbabilisticSerialPhaseState

/-!
# probabilistic_serial_fractional_assignment_row_sum

Topic: social_choice   Node: 730bebeec0b9

Provenance: helper lemma. step towards probabilistic_serial_line_metric_sharp_linear_distortion

Under probabilistic serial each agent consumes exactly one unit in total: the row sums of the probabilistic serial assignment are 1.
-/

private noncomputable def yEats (n : ℕ) (pref : Fin n → Equiv.Perm (Fin n))
    (s : (Fin n → ℝ) × (Fin n → Fin n → ℝ)) (i j : Fin n) : Prop :=
  0 < s.1 j ∧ ∀ j', 0 < s.1 j' → (pref i).symm j ≤ (pref i).symm j'

private noncomputable def yCnt (n : ℕ) (pref : Fin n → Equiv.Perm (Fin n))
    (s : (Fin n → ℝ) × (Fin n → Fin n → ℝ)) (j : Fin n) : ℕ :=
  open Classical in (Finset.univ.filter (fun i => yEats n pref s i j)).card

private noncomputable def yS (n : ℕ) (pref : Fin n → Equiv.Perm (Fin n))
    (s : (Fin n → ℝ) × (Fin n → Fin n → ℝ)) : Finset (Fin n) :=
  open Classical in Finset.univ.filter (fun j => 0 < yCnt n pref s j)

private noncomputable def yT (n : ℕ) (pref : Fin n → Equiv.Perm (Fin n))
    (s : (Fin n → ℝ) × (Fin n → Fin n → ℝ)) : ℝ :=
  if h : (yS n pref s).Nonempty then (yS n pref s).inf' h (fun j => s.1 j / (yCnt n pref s j)) else 0

open Classical in
private lemma yCnt_eq' (n : ℕ) (pref : Fin n → Equiv.Perm (Fin n))
    (s : (Fin n → ℝ) × (Fin n → Fin n → ℝ)) (j : Fin n) :
    yCnt n pref s j = (Finset.univ.filter (fun i => yEats n pref s i j)).card := rfl

private lemma yCnt_eq (n : ℕ) (pref : Fin n → Equiv.Perm (Fin n))
    (s : (Fin n → ℝ) × (Fin n → Fin n → ℝ)) (j : Fin n) :
    yCnt n pref s j =
      (Finset.univ.filter (fun i => 0 < s.1 j ∧ ∀ j', 0 < s.1 j' → (pref i).symm j ≤ (pref i).symm j')).card := by
  classical
  rw [yCnt_eq']
  congr 1
  exact Finset.filter_congr (fun i _ => Iff.rfl)

private lemma yS_eq (n : ℕ) (pref : Fin n → Equiv.Perm (Fin n))
    (s : (Fin n → ℝ) × (Fin n → Fin n → ℝ)) :
    yS n pref s =
      Finset.univ.filter (fun j => 0 < (Finset.univ.filter (fun i => 0 < s.1 j ∧ ∀ j', 0 < s.1 j' → (pref i).symm j ≤ (pref i).symm j')).card) := by
  classical
  unfold yS
  exact Finset.filter_congr (fun j _ => by rw [yCnt_eq])

private lemma yT_eq (n : ℕ) (pref : Fin n → Equiv.Perm (Fin n))
    (s : (Fin n → ℝ) × (Fin n → Fin n → ℝ)) :
    yT n pref s =
      (if h : (Finset.univ.filter (fun j => 0 < (Finset.univ.filter (fun i => 0 < s.1 j ∧ ∀ j', 0 < s.1 j' → (pref i).symm j ≤ (pref i).symm j')).card)).Nonempty
        then (Finset.univ.filter (fun j => 0 < (Finset.univ.filter (fun i => 0 < s.1 j ∧ ∀ j', 0 < s.1 j' → (pref i).symm j ≤ (pref i).symm j')).card)).inf' h (fun j => s.1 j / ((Finset.univ.filter (fun i => 0 < s.1 j ∧ ∀ j', 0 < s.1 j' → (pref i).symm j ≤ (pref i).symm j')).card : ℝ))
        else 0) := by
  classical
  unfold yT
  rw [yS_eq]
  split
  · rename_i h
    exact Finset.inf'_congr h rfl (fun x _ => by rw [yCnt_eq])
  · rfl

open Classical in
private lemma yphase_eq (n : ℕ) (pref : Fin n → Equiv.Perm (Fin n))
    (s : (Fin n → ℝ) × (Fin n → Fin n → ℝ)) :
    probabilistic_serial_phase n pref s =
      ((fun j => s.1 j - yT n pref s * (yCnt n pref s j : ℝ)),
       (fun i j => s.2 i j + if yEats n pref s i j then yT n pref s else 0)) := by
  classical
  simp only [probabilistic_serial_phase]
  rw [← yT_eq n pref s]
  simp only [Prod.mk.injEq]
  constructor
  · funext j
    rw [← yCnt_eq n pref s j]
  · funext i j
    by_cases h : yEats n pref s i j
    · rw [if_pos h]
      have h' : (0 < s.1 j ∧ ∀ j', 0 < s.1 j' → (pref i).symm j ≤ (pref i).symm j') := h
      rw [if_pos h']
    · rw [if_neg h]
      have h' : ¬ (0 < s.1 j ∧ ∀ j', 0 < s.1 j' → (pref i).symm j ≤ (pref i).symm j') := h
      rw [if_neg h']

private lemma yT_nonneg (n : ℕ) (pref : Fin n → Equiv.Perm (Fin n))
    (s : (Fin n → ℝ) × (Fin n → Fin n → ℝ)) (hpos : ∀ j, 0 ≤ s.1 j) :
    0 ≤ yT n pref s := by
  classical
  by_cases hS : (yS n pref s).Nonempty
  · obtain ⟨j0, _hj0mem, hj0eq⟩ := Finset.exists_mem_eq_inf' hS (fun j => s.1 j / (yCnt n pref s j))
    rw [yT, dif_pos hS, hj0eq]
    exact div_nonneg (hpos j0) (Nat.cast_nonneg _)
  · rw [yT, dif_neg hS]

private lemma yT_mul_le (n : ℕ) (pref : Fin n → Equiv.Perm (Fin n))
    (s : (Fin n → ℝ) × (Fin n → Fin n → ℝ)) (hpos : ∀ j, 0 ≤ s.1 j) (j : Fin n) :
    yT n pref s * (yCnt n pref s j : ℝ) ≤ s.1 j := by
  classical
  rcases Nat.eq_zero_or_pos (yCnt n pref s j) with hz | hpos'
  · rw [hz, Nat.cast_zero, mul_zero]
    exact hpos j
  · have hmem : j ∈ yS n pref s := by
      rw [yS, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hpos'⟩
    rw [yT, dif_pos ⟨j, hmem⟩]
    have hle := Finset.inf'_le (s := yS n pref s) (f := fun j => s.1 j / (yCnt n pref s j)) hmem
    have hc : (0:ℝ) < (yCnt n pref s j : ℝ) := by exact_mod_cast hpos'
    calc (yS n pref s).inf' _ (fun j => s.1 j / (yCnt n pref s j)) * (yCnt n pref s j : ℝ)
        ≤ (s.1 j / (yCnt n pref s j : ℝ)) * (yCnt n pref s j : ℝ) :=
          mul_le_mul_of_nonneg_right hle (le_of_lt hc)
      _ = s.1 j := div_mul_cancel₀ _ (ne_of_gt hc)

private lemma yphase_fst (n : ℕ) (pref : Fin n → Equiv.Perm (Fin n))
    (s : (Fin n → ℝ) × (Fin n → Fin n → ℝ)) (hpos : ∀ j, 0 ≤ s.1 j) (j : Fin n) :
    0 ≤ (probabilistic_serial_phase n pref s).1 j ∧
      (probabilistic_serial_phase n pref s).1 j ≤ s.1 j := by
  have h := congrFun (congrArg Prod.fst (yphase_eq n pref s)) j
  rw [h]
  refine ⟨?_, ?_⟩
  · have := yT_mul_le n pref s hpos j
    linarith
  · have h1 := yT_nonneg n pref s hpos
    have h2 := Nat.cast_nonneg (α := ℝ) (yCnt n pref s j)
    nlinarith

private lemma yargmin (n : ℕ) (pref : Fin n → Equiv.Perm (Fin n))
    (s : (Fin n → ℝ) × (Fin n → Fin n → ℝ)) (hp : ∃ j, 0 < s.1 j) (i : Fin n) :
    ∃ j, yEats n pref s i j := by
  classical
  obtain ⟨j0, hj0⟩ := hp
  let P : Finset (Fin n) := Finset.univ.filter (fun j => 0 < s.1 j)
  have hP : P.Nonempty := ⟨j0, by simp [P, hj0]⟩
  let Q : Finset (Fin n) := P.image (pref i).symm
  have hQ : Q.Nonempty := ⟨(pref i).symm j0, by simp [Q, P, hj0]⟩
  obtain ⟨j, hjP, hjQ⟩ := Finset.mem_image.mp (Finset.min'_mem Q hQ)
  refine ⟨j, ?_, ?_⟩
  · exact (Finset.mem_filter.mp hjP).2
  · intro j' hj'
    have hj'P : j' ∈ P := by simp [P, hj']
    have hmem : (pref i).symm j' ∈ Q := Finset.mem_image.mpr ⟨j', hj'P, rfl⟩
    have hmin := (Finset.min'_eq_iff Q hQ (Q.min' hQ)).mp rfl
    rw [hjQ]
    exact hmin.2 _ hmem

private lemma yeats_unique (n : ℕ) (pref : Fin n → Equiv.Perm (Fin n))
    (s : (Fin n → ℝ) × (Fin n → Fin n → ℝ)) (hp : ∃ j, 0 < s.1 j) (i : Fin n) :
    ∃! j, yEats n pref s i j := by
  obtain ⟨j0, hj0⟩ := yargmin n pref s hp i
  refine ⟨j0, hj0, ?_⟩
  intro j1 hj1
  have h1 : (pref i).symm j1 ≤ (pref i).symm j0 := hj1.2 j0 hj0.1
  have h2 : (pref i).symm j0 ≤ (pref i).symm j1 := hj0.2 j1 hj1.1
  have heq : (pref i).symm j1 = (pref i).symm j0 := le_antisymm h1 h2
  calc j1 = (pref i) ((pref i).symm j1) := (Equiv.apply_symm_apply (pref i) j1).symm
    _ = (pref i) ((pref i).symm j0) := by rw [heq]
    _ = j0 := Equiv.apply_symm_apply (pref i) j0

open Classical in
private lemma ysum_eats (n : ℕ) (pref : Fin n → Equiv.Perm (Fin n))
    (s : (Fin n → ℝ) × (Fin n → Fin n → ℝ)) (hp : ∃ j, 0 < s.1 j) (i : Fin n) :
    ∑ j, (if yEats n pref s i j then (1:ℝ) else 0) = 1 := by
  classical
  obtain ⟨j0, hj0, huniq⟩ := yeats_unique n pref s hp i
  rw [Finset.sum_eq_single j0]
  · rw [if_pos hj0]
  · intro b _ hb
    rw [if_neg]
    intro hb'
    exact hb (huniq b hb')
  · intro h; exact absurd (Finset.mem_univ j0) h

private lemma ycnt_sum (n : ℕ) (pref : Fin n → Equiv.Perm (Fin n))
    (s : (Fin n → ℝ) × (Fin n → Fin n → ℝ)) (hp : ∃ j, 0 < s.1 j) :
    ∑ j, (yCnt n pref s j : ℝ) = n := by
  classical
  have h1 : ∀ j, (yCnt n pref s j : ℝ) = ∑ i, (if yEats n pref s i j then (1:ℝ) else 0) := by
    intro j
    rw [yCnt_eq', Finset.sum_boole]
  calc ∑ j, (yCnt n pref s j : ℝ)
      = ∑ j, ∑ i, (if yEats n pref s i j then (1:ℝ) else 0) := by simp_rw [h1]
    _ = ∑ i, ∑ j, (if yEats n pref s i j then (1:ℝ) else 0) := Finset.sum_comm
    _ = ∑ i, (1:ℝ) := Finset.sum_congr rfl (fun i _ => ysum_eats n pref s hp i)
    _ = n := by simp

private lemma yS_nonempty_exists (n : ℕ) (pref : Fin n → Equiv.Perm (Fin n))
    (s : (Fin n → ℝ) × (Fin n → Fin n → ℝ)) (hS : (yS n pref s).Nonempty) :
    ∃ j, 0 < s.1 j := by
  classical
  obtain ⟨j, hj⟩ := hS
  rw [yS, Finset.mem_filter, yCnt_eq'] at hj
  obtain ⟨i, hi⟩ := Finset.card_pos.mp hj.2
  exact ⟨j, (Finset.mem_filter.mp hi).2.1⟩

private lemma yphase_total (n : ℕ) (pref : Fin n → Equiv.Perm (Fin n))
    (s : (Fin n → ℝ) × (Fin n → Fin n → ℝ)) :
    ∑ j, (probabilistic_serial_phase n pref s).1 j = ∑ j, s.1 j - yT n pref s * n := by
  classical
  rw [yphase_eq]
  change ∑ j, (s.1 j - yT n pref s * (yCnt n pref s j : ℝ)) = ∑ j, s.1 j - yT n pref s * n
  by_cases hS : (yS n pref s).Nonempty
  · have hp := yS_nonempty_exists n pref s hS
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ycnt_sum n pref s hp]
  · have ht : yT n pref s = 0 := by
      rw [yT]; exact dif_neg hS
    have hcnt : ∀ j, yCnt n pref s j = 0 := by
      intro j
      by_contra h
      exact hS ⟨j, by rw [yS, Finset.mem_filter]; exact ⟨Finset.mem_univ _, Nat.pos_of_ne_zero h⟩⟩
    simp [ht, hcnt]

open Classical in
private lemma yphase_row (n : ℕ) (pref : Fin n → Equiv.Perm (Fin n))
    (s : (Fin n → ℝ) × (Fin n → Fin n → ℝ)) (i : Fin n) :
    ∑ j, (probabilistic_serial_phase n pref s).2 i j = ∑ j, s.2 i j + yT n pref s := by
  classical
  rw [yphase_eq]
  change ∑ j, (s.2 i j + if yEats n pref s i j then yT n pref s else 0) = ∑ j, s.2 i j + yT n pref s
  by_cases hS : (yS n pref s).Nonempty
  · have hp := yS_nonempty_exists n pref s hS
    have hsum : ∑ j, (if yEats n pref s i j then yT n pref s else 0) = yT n pref s := by
      calc ∑ j, (if yEats n pref s i j then yT n pref s else 0)
          = ∑ j, yT n pref s * (if yEats n pref s i j then (1:ℝ) else 0) := by
            apply Finset.sum_congr rfl
            intro j _
            by_cases h : yEats n pref s i j <;> simp [h]
        _ = yT n pref s * ∑ j, (if yEats n pref s i j then (1:ℝ) else 0) := by
            rw [Finset.mul_sum]
        _ = yT n pref s * 1 := by rw [ysum_eats n pref s hp i]
        _ = yT n pref s := by ring
    rw [Finset.sum_add_distrib, hsum]
  · have ht : yT n pref s = 0 := by
      rw [yT]; exact dif_neg hS
    have he : ∀ j, ¬ yEats n pref s i j := by
      intro j h
      refine hS ⟨j, ?_⟩
      rw [yS, Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [yCnt_eq']
      exact Finset.card_pos.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩⟩
    simp [ht, he]

private noncomputable def yCap (n : ℕ) (pref : Fin n → Equiv.Perm (Fin n)) (k : ℕ) : Fin n → ℝ :=
  (probabilistic_serial_phase_state n pref k).1

private noncomputable def yTot (n : ℕ) (pref : Fin n → Equiv.Perm (Fin n)) (k : ℕ) : ℝ :=
  ∑ j, yCap n pref k j

private noncomputable def yD (n : ℕ) (pref : Fin n → Equiv.Perm (Fin n)) (k : ℕ) : ℝ :=
  yT n pref (probabilistic_serial_phase_state n pref k)

private noncomputable def yX (n : ℕ) (pref : Fin n → Equiv.Perm (Fin n)) (k : ℕ) (i : Fin n) : ℝ :=
  ∑ j, (probabilistic_serial_phase_state n pref k).2 i j

private lemma ystate_succ (n : ℕ) (pref : Fin n → Equiv.Perm (Fin n)) (k : ℕ) :
    probabilistic_serial_phase_state n pref (k + 1) =
      probabilistic_serial_phase n pref (probabilistic_serial_phase_state n pref k) := by
  simp [probabilistic_serial_phase_state, Function.iterate_succ_apply']

private lemma yCap_nonneg (n : ℕ) (pref : Fin n → Equiv.Perm (Fin n)) (k : ℕ) :
    ∀ j, 0 ≤ yCap n pref k j := by
  induction k with
  | zero => intro j; simp [yCap, probabilistic_serial_phase_state]
  | succ k ih =>
    intro j
    have h := (yphase_fst n pref _ ih j).1
    rw [← ystate_succ] at h
    exact h

private lemma yCap_le (n : ℕ) (pref : Fin n → Equiv.Perm (Fin n)) (k : ℕ) :
    ∀ j, yCap n pref (k + 1) j ≤ yCap n pref k j := by
  intro j
  have h := (yphase_fst n pref _ (yCap_nonneg n pref k) j).2
  rw [← ystate_succ] at h
  exact h

private lemma yTot_nonneg (n : ℕ) (pref : Fin n → Equiv.Perm (Fin n)) (k : ℕ) :
    0 ≤ yTot n pref k :=
  Finset.sum_nonneg (fun j _ => yCap_nonneg n pref k j)

private lemma ystep (n : ℕ) (pref : Fin n → Equiv.Perm (Fin n)) (k : ℕ) :
    yTot n pref (k + 1) = yTot n pref k - yD n pref k * n := by
  have h := yphase_total n pref (probabilistic_serial_phase_state n pref k)
  rw [← ystate_succ] at h
  simpa [yTot, yCap, yD, yT] using h

private lemma yrow_step (n : ℕ) (pref : Fin n → Equiv.Perm (Fin n)) (k : ℕ) (i : Fin n) :
    yX n pref (k + 1) i = yX n pref k i + yD n pref k := by
  have h := yphase_row n pref (probabilistic_serial_phase_state n pref k) i
  rw [← ystate_succ] at h
  simpa [yX, yD, yT] using h

private noncomputable def yZ (n : ℕ) (pref : Fin n → Equiv.Perm (Fin n)) (k : ℕ) : Finset (Fin n) :=
  open Classical in Finset.univ.filter (fun j => yCap n pref k j = 0)

private lemma yZ_mono (n : ℕ) (pref : Fin n → Equiv.Perm (Fin n)) (k : ℕ) :
    yZ n pref k ⊆ yZ n pref (k+1) := by
  classical
  intro j hj
  rw [yZ, Finset.mem_filter] at hj ⊢
  refine ⟨Finset.mem_univ _, ?_⟩
  have h1 := yCap_le n pref k j
  have h2 := yCap_nonneg n pref (k+1) j
  rw [hj.2] at h1
  linarith

private lemma yTot_pos_iff (n : ℕ) (pref : Fin n → Equiv.Perm (Fin n)) (k : ℕ) :
    0 < yTot n pref k ↔ ∃ j, 0 < yCap n pref k j := by
  constructor
  · intro h
    by_contra hc
    have h0 : ∀ j, yCap n pref k j = 0 := by
      intro j
      by_contra hj
      exact hc ⟨j, lt_of_le_of_ne (yCap_nonneg n pref k j) (Ne.symm hj)⟩
    have hz : yTot n pref k = 0 := Finset.sum_eq_zero (fun j _ => h0 j)
    linarith
  · rintro ⟨j, hj⟩
    exact lt_of_lt_of_le hj (Finset.single_le_sum (f := yCap n pref k)
      (fun i _ => yCap_nonneg n pref k i) (Finset.mem_univ j))

private lemma yTot_zero_all (n : ℕ) (pref : Fin n → Equiv.Perm (Fin n)) (k : ℕ)
    (h : yTot n pref k = 0) : ∀ j, yCap n pref k j = 0 := by
  intro j
  have h1 := yCap_nonneg n pref k j
  have h2 : yCap n pref k j ≤ yTot n pref k :=
    Finset.single_le_sum (f := yCap n pref k) (fun i _ => yCap_nonneg n pref k i) (Finset.mem_univ j)
  linarith

private lemma yzero_item (n : ℕ) (pref : Fin n → Equiv.Perm (Fin n)) (k : ℕ)
    (hk : 0 < yTot n pref k) :
    ∃ j, 0 < yCap n pref k j ∧ yCap n pref (k+1) j = 0 := by
  classical
  obtain ⟨j1, hj1⟩ := (yTot_pos_iff n pref k).mp hk
  set s := probabilistic_serial_phase_state n pref k with hs
  have hspos : ∃ j, 0 < s.1 j := ⟨j1, by simpa [hs, yCap] using hj1⟩
  haveI : Nonempty (Fin n) := ⟨j1⟩
  obtain ⟨i0⟩ := ‹Nonempty (Fin n)›
  obtain ⟨je, hje⟩ := yargmin n pref s hspos i0
  have hS : (yS n pref s).Nonempty := by
    refine ⟨je, ?_⟩
    rw [yS, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [yCnt_eq']
    exact Finset.card_pos.mpr ⟨i0, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hje⟩⟩
  obtain ⟨j0, hj0mem, hj0eq⟩ := Finset.exists_mem_eq_inf' hS (fun j => s.1 j / (yCnt n pref s j))
  rw [yS, Finset.mem_filter] at hj0mem
  have hcnt0 : yCnt n pref s j0 ≠ 0 := ne_of_gt hj0mem.2
  have hcnt0R : (yCnt n pref s j0 : ℝ) ≠ 0 := by simpa using hcnt0
  have hj0pos : 0 < yCap n pref k j0 := by
    have hh := hj0mem.2
    rw [yCnt_eq'] at hh
    obtain ⟨i, hi⟩ := Finset.card_pos.mp hh
    exact (Finset.mem_filter.mp hi).2.1
  refine ⟨j0, hj0pos, ?_⟩
  have hT : yT n pref s = s.1 j0 / (yCnt n pref s j0 : ℝ) := by
    rw [yT, dif_pos hS]; exact hj0eq
  have hcap : yCap n pref (k+1) j0 = s.1 j0 - yT n pref s * (yCnt n pref s j0 : ℝ) := by
    have h := congrFun (congrArg Prod.fst (yphase_eq n pref s)) j0
    simpa [yCap, hs, ystate_succ] using h
  rw [hcap, hT, div_mul_cancel₀ _ hcnt0R, sub_self]

private lemma yZ_card (n : ℕ) (pref : Fin n → Equiv.Perm (Fin n)) :
    ∀ k, k ≤ n → k ≤ (yZ n pref k).card := by
  intro k
  induction k with
  | zero => intro _; exact Nat.zero_le _
  | succ k ih =>
    intro hk
    have hkn : k < n := Nat.lt_of_succ_le hk
    have hprev : k ≤ (yZ n pref k).card := ih (Nat.le_of_lt hkn)
    by_cases ht : 0 < yTot n pref k
    · obtain ⟨j, hjpos, hjzero⟩ := yzero_item n pref k ht
      have hmem : j ∈ yZ n pref (k+1) := by
        rw [yZ, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hjzero⟩
      have hnot : j ∉ yZ n pref k := by
        rw [yZ, Finset.mem_filter]
        rintro ⟨-, hz⟩
        rw [hz] at hjpos; exact lt_irrefl _ hjpos
      have hsub : yZ n pref k ⊆ (yZ n pref (k+1)).erase j := by
        intro x hx
        rw [Finset.mem_erase]
        exact ⟨by rintro rfl; exact hnot hx, yZ_mono n pref k hx⟩
      have h1 : (yZ n pref k).card ≤ ((yZ n pref (k+1)).erase j).card := Finset.card_le_card hsub
      have h2 : ((yZ n pref (k+1)).erase j).card + 1 = (yZ n pref (k+1)).card :=
        Finset.card_erase_add_one hmem
      omega
    · have hz : yTot n pref k = 0 := le_antisymm (not_lt.mp ht) (yTot_nonneg n pref k)
      have hall := yTot_zero_all n pref k hz
      have hall' : ∀ j, yCap n pref (k+1) j = 0 := by
        intro j
        have h1 := yCap_le n pref k j
        have h2 := yCap_nonneg n pref (k+1) j
        rw [hall j] at h1
        linarith
      have huniv : yZ n pref (k+1) = Finset.univ := by
        refine Finset.eq_univ_iff_forall.mpr (fun j => ?_)
        rw [yZ, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hall' j⟩
      rw [huniv, Finset.card_univ, Fintype.card_fin]
      exact hk

private lemma yTot_final (n : ℕ) (pref : Fin n → Equiv.Perm (Fin n)) :
    yTot n pref n = 0 := by
  have h : n ≤ (yZ n pref n).card := yZ_card n pref n le_rfl
  have hle : (yZ n pref n).card ≤ n := by
    have hc := Finset.card_le_univ (s := yZ n pref n)
    rwa [Fintype.card_fin] at hc
  have hcard : (yZ n pref n).card = n := le_antisymm hle h
  have huniv : yZ n pref n = Finset.univ :=
    Finset.eq_univ_of_card _ (by rw [Fintype.card_fin]; exact hcard)
  apply Finset.sum_eq_zero
  intro j _
  have hmem : j ∈ yZ n pref n := by rw [huniv]; exact Finset.mem_univ j
  rw [yZ, Finset.mem_filter] at hmem
  exact hmem.2

private noncomputable def yP (n : ℕ) (pref : Fin n → Equiv.Perm (Fin n)) (k : ℕ) : ℝ :=
  ∑ i ∈ Finset.range k, yD n pref i

private lemma yTot_form (n : ℕ) (pref : Fin n → Equiv.Perm (Fin n)) (k : ℕ) :
    yTot n pref k = n - yP n pref k * n := by
  induction k with
  | zero =>
    have h : yTot n pref 0 = n := by
      simp [yTot, yCap, probabilistic_serial_phase_state]
    rw [h]; simp [yP]
  | succ k ih =>
    rw [ystep, ih]
    simp only [yP, Finset.sum_range_succ]
    ring

private lemma yrow_form (n : ℕ) (pref : Fin n → Equiv.Perm (Fin n)) (k : ℕ) (i : Fin n) :
    yX n pref k i = yP n pref k := by
  induction k with
  | zero =>
    have h : yX n pref 0 i = 0 := by
      simp [yX, probabilistic_serial_phase_state]
    rw [h]; simp [yP]
  | succ k ih =>
    rw [yrow_step, ih]
    simp only [yP, Finset.sum_range_succ]

/-- Every agent eats a total of exactly one unit under probabilistic serial: the row sums of the PS assignment equal 1. -/
theorem probabilistic_serial_fractional_assignment_row_sum (n : ℕ) (hn : 1 ≤ n) (pref : Fin n → Equiv.Perm (Fin n)) (i : Fin n) : ∑ j, probabilistic_serial_fractional_assignment n pref i j = 1 := by
  have hfin : yTot n pref n = 0 := yTot_final n pref
  rw [yTot_form] at hfin
  have hn0 : (n : ℝ) ≠ 0 := by
    have : n ≠ 0 := by omega
    exact_mod_cast this
  have hP : yP n pref n = 1 := by
    have h2 : yP n pref n * (n:ℝ) = 1 * (n:ℝ) := by rw [one_mul]; linarith
    exact mul_right_cancel₀ hn0 h2
  have hrow : ∑ j, probabilistic_serial_fractional_assignment n pref i j = yP n pref n := by
    have e : ∑ j, probabilistic_serial_fractional_assignment n pref i j = yX n pref n i := rfl
    rw [e, yrow_form]
  rw [hrow, hP]
