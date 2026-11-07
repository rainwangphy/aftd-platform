import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ProbabilisticSerialLineCost
import AFTD.Kb.GameTheoryEconomics.LineMinMatchingCost
import AFTD.Kb.GameTheoryEconomics.IsLineDistancePreferenceProfile
import AFTD.Kb.GameTheoryEconomics.ProbabilisticSerialLineItemWait
import AFTD.Kb.GameTheoryEconomics.ProbabilisticSerialPhase
import AFTD.Kb.GameTheoryEconomics.ProbabilisticSerialFractionalAssignment
import AFTD.Kb.GameTheoryEconomics.ProbabilisticSerialPhaseState
import AFTD.Kb.GameTheoryEconomics.ProbabilisticSerialPhaseLength

/-!
# probabilistic_serial_line_cost_le_add_item_wait

Topic: social_choice   Node: 9c655a9762d4

Provenance: helper lemma. Reduction step for OP-1158 (probabilistic serial on the line, PS <= n*OPT); reduction found 2026-11-07 for IN-608, experiments 17916, 17917

For n agents at real positions a and n items at real positions b, each agent ranking the items by distance (ties broken arbitrarily), the probabilistic serial cost is at most OPT (the minimum perfect-matching cost) plus the sum over items of their waiting costs.
-/

theorem ps_wait_phase_fst_le_and_nonneg (n : ℕ) (pref : Fin n → Equiv.Perm (Fin n))
    (s : (Fin n → ℝ) × (Fin n → Fin n → ℝ)) (hs : ∀ j, 0 ≤ s.1 j) (j : Fin n) :
    0 ≤ (probabilistic_serial_phase n pref s).1 j ∧ (probabilistic_serial_phase n pref s).1 j ≤ s.1 j := by
  classical
  unfold probabilistic_serial_phase
  simp only
  set S := Finset.univ.filter (fun j => 0 < (Finset.univ.filter (fun i =>
      0 < s.1 j ∧ ∀ j', 0 < s.1 j' → (pref i).symm j ≤ (pref i).symm j')).card) with hS
  split_ifs with h
  · set c : Fin n → ℕ := fun j => (Finset.univ.filter (fun i =>
      0 < s.1 j ∧ ∀ j', 0 < s.1 j' → (pref i).symm j ≤ (pref i).symm j')).card with hc
    have ht0 : 0 ≤ S.inf' h (fun j => s.1 j / (c j : ℝ)) := by
      rw [Finset.le_inf'_iff]
      intro k _
      exact div_nonneg (hs k) (Nat.cast_nonneg _)
    have hcn : (0 : ℝ) ≤ (c j : ℝ) := Nat.cast_nonneg _
    constructor
    · by_cases hj : j ∈ S
      · have hle := Finset.inf'_le (fun j => s.1 j / (c j : ℝ)) hj
        have hpos : (0 : ℝ) < c j := by
          have := (Finset.mem_filter.mp hj).2
          exact_mod_cast this
        have := (le_div_iff₀ hpos).mp hle
        show 0 ≤ s.1 j - S.inf' h (fun j => s.1 j / (c j : ℝ)) * (c j : ℝ)
        linarith
      · have h0 : c j = 0 := by
          by_contra hne
          exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _, Nat.pos_of_ne_zero hne⟩)
        show 0 ≤ s.1 j - S.inf' h (fun j => s.1 j / (c j : ℝ)) * (c j : ℝ)
        rw [h0]; simp [hs j]
    · show s.1 j - S.inf' h (fun j => s.1 j / (c j : ℝ)) * (c j : ℝ) ≤ s.1 j
      nlinarith
  · simp [hs j]

abbrev ps_wait_eats (n : ℕ) (pref : Fin n → Equiv.Perm (Fin n))
    (s : (Fin n → ℝ) × (Fin n → Fin n → ℝ)) (i j : Fin n) : Prop :=
  0 < s.1 j ∧ ∀ j', 0 < s.1 j' → (pref i).symm j ≤ (pref i).symm j'

noncomputable def ps_wait_time (n : ℕ) (pref : Fin n → Equiv.Perm (Fin n))
    (s : (Fin n → ℝ) × (Fin n → Fin n → ℝ)) : ℝ :=
  open Classical in
  let cnt : Fin n → ℕ := fun j => (Finset.univ.filter (fun i => ps_wait_eats n pref s i j)).card
  let S := Finset.univ.filter (fun j => 0 < cnt j)
  if h : S.Nonempty then S.inf' h (fun j => s.1 j / cnt j) else 0

theorem ps_wait_phase_eq (n : ℕ) (pref : Fin n → Equiv.Perm (Fin n))
    (s : (Fin n → ℝ) × (Fin n → Fin n → ℝ)) :
    probabilistic_serial_phase n pref s =
      (open Classical in fun j => s.1 j - ps_wait_time n pref s *
          (Finset.univ.filter (fun i => ps_wait_eats n pref s i j)).card,
       open Classical in fun i j => s.2 i j + if ps_wait_eats n pref s i j then ps_wait_time n pref s else 0) := by
  rfl

theorem ps_wait_eats_unique (n : ℕ) (pref : Fin n → Equiv.Perm (Fin n))
    (s : (Fin n → ℝ) × (Fin n → Fin n → ℝ)) (i j j' : Fin n)
    (h : ps_wait_eats n pref s i j) (h' : ps_wait_eats n pref s i j') : j = j' := by
  have h1 := h.2 j' h'.1
  have h2 := h'.2 j h.1
  exact (pref i).symm.injective (le_antisymm h1 h2)

theorem ps_wait_eats_exists (n : ℕ) (pref : Fin n → Equiv.Perm (Fin n))
    (s : (Fin n → ℝ) × (Fin n → Fin n → ℝ)) (hA : ∃ j, 0 < s.1 j) (i : Fin n) :
    ∃ j, ps_wait_eats n pref s i j := by
  classical
  have hne : (Finset.univ.filter (fun j => 0 < s.1 j)).Nonempty := by
    obtain ⟨j, hj⟩ := hA; exact ⟨j, by simp [hj]⟩
  obtain ⟨j, hj, hmin⟩ := Finset.exists_min_image _ (fun j => (pref i).symm j) hne
  refine ⟨j, (Finset.mem_filter.mp hj).2, fun j' hj' => hmin j' (by simp [hj'])⟩

theorem ps_wait_eats_nearest {n : ℕ} (a b : Fin n → ℝ) (pref : Fin n → Equiv.Perm (Fin n))
    (hp : is_line_distance_preference_profile a b pref)
    (s : (Fin n → ℝ) × (Fin n → Fin n → ℝ)) (i j j' : Fin n)
    (h : ps_wait_eats n pref s i j) (hj' : 0 < s.1 j') : |a i - b j| ≤ |a i - b j'| := by
  have hle := h.2 j' hj'
  rcases lt_or_eq_of_le hle with hlt | heq
  · have := hp i _ _ hlt
    simpa using this
  · have : j = j' := (pref i).symm.injective heq
    rw [this]

open Classical in
theorem ps_wait_card_sum (n : ℕ) (pref : Fin n → Equiv.Perm (Fin n))
    (s : (Fin n → ℝ) × (Fin n → Fin n → ℝ)) (hA : ∃ j, 0 < s.1 j) :
    (∑ j, ((Finset.univ.filter (fun i => ps_wait_eats n pref s i j)).card : ℝ)) = n := by
  classical
  have : (∑ j, (Finset.univ.filter (fun i => ps_wait_eats n pref s i j)).card) = n := by
    rw [← Finset.card_sigma]
    have : ∀ i, (Finset.univ.filter (fun j => ps_wait_eats n pref s i j)).card = 1 := by
      intro i
      obtain ⟨j, hj⟩ := ps_wait_eats_exists n pref s hA i
      rw [Finset.card_eq_one]
      refine ⟨j, ?_⟩
      ext j'
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun h' => ps_wait_eats_unique n pref s i j' j h' hj, fun e => e ▸ hj⟩
    calc _ = ∑ i : Fin n, (Finset.univ.filter (fun j => ps_wait_eats n pref s i j)).card := by
            rw [← Finset.card_sigma]
            refine Finset.card_bij (fun p _ => ⟨p.2, p.1⟩) ?_ ?_ ?_
            · intro p hp; simp at hp ⊢; exact hp
            · intro p _ q _ e; simp at e; ext <;> simp [e.1, e.2]
            · intro q hq; refine ⟨⟨q.2, q.1⟩, by simpa using hq, rfl⟩
      _ = n := by simp [this]
  exact_mod_cast this

theorem ps_wait_time_nonneg (n : ℕ) (pref : Fin n → Equiv.Perm (Fin n))
    (s : (Fin n → ℝ) × (Fin n → Fin n → ℝ)) (hs : ∀ j, 0 ≤ s.1 j) : 0 ≤ ps_wait_time n pref s := by
  classical
  unfold ps_wait_time
  simp only
  split_ifs with h
  · rw [Finset.le_inf'_iff]
    intro k _
    exact div_nonneg (hs k) (Nat.cast_nonneg _)
  · exact le_rfl

open Classical in
theorem ps_wait_phase_cost_le {n : ℕ} (a b : Fin n → ℝ) (pref : Fin n → Equiv.Perm (Fin n))
    (hp : is_line_distance_preference_profile a b pref)
    (s : (Fin n → ℝ) × (Fin n → Fin n → ℝ)) (σ : Equiv.Perm (Fin n)) (L : ℝ) (hL0 : 0 ≤ L)
    (hL : (∃ j, 0 < s.1 j) → L = ps_wait_time n pref s) :
    ∑ i, ∑ j, (if ps_wait_eats n pref s i j then ps_wait_time n pref s else 0) * |a i - b j| ≤
      L * ∑ i, |a i - b (σ i)| +
      ∑ m, (if h : s.1 m ≤ 0 ∧ (Finset.univ.filter (fun j' => 0 < s.1 j')).Nonempty
        then L * (Finset.univ.filter (fun j' => 0 < s.1 j')).inf' h.2 (fun j' => |b m - b j'|)
        else 0) := by
  by_cases hA : ∃ j, 0 < s.1 j
  · have hLt := hL hA
    rw [← hLt]
    have hne : (Finset.univ.filter (fun j' => 0 < s.1 j')).Nonempty := by
      obtain ⟨j, hj⟩ := hA; exact ⟨j, by simp [hj]⟩
    have hrhs : ∀ m, (if h : s.1 m ≤ 0 ∧ (Finset.univ.filter (fun j' => 0 < s.1 j')).Nonempty
        then L * (Finset.univ.filter (fun j' => 0 < s.1 j')).inf' h.2 (fun j' => |b m - b j'|)
        else 0) = L * (if h : s.1 m ≤ 0 then
          (Finset.univ.filter (fun j' => 0 < s.1 j')).inf' hne (fun j' => |b m - b j'|) else 0) := by
      intro m
      by_cases hm : s.1 m ≤ 0
      · rw [dif_pos ⟨hm, hne⟩, dif_pos hm]
      · rw [dif_neg (fun h => hm h.1), dif_neg hm, mul_zero]
    simp_rw [hrhs]
    rw [← Finset.mul_sum, ← mul_add]
    have hσ : ∑ m, (if h : s.1 m ≤ 0 then
          (Finset.univ.filter (fun j' => 0 < s.1 j')).inf' hne (fun j' => |b m - b j'|) else 0) =
        ∑ i, (if h : s.1 (σ i) ≤ 0 then
          (Finset.univ.filter (fun j' => 0 < s.1 j')).inf' hne (fun j' => |b (σ i) - b j'|) else 0) :=
      (Equiv.sum_comp σ (fun m => if h : s.1 m ≤ 0 then
          (Finset.univ.filter (fun j' => 0 < s.1 j')).inf' hne (fun j' => |b m - b j'|) else 0)).symm
    rw [hσ, ← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _
    obtain ⟨ji, hji⟩ := ps_wait_eats_exists n pref s hA i
    rw [Finset.sum_eq_single ji]
    · rw [if_pos hji]
      apply mul_le_mul_of_nonneg_left _ hL0
      by_cases hm : s.1 (σ i) ≤ 0
      · rw [dif_pos hm]
        obtain ⟨j', hj'mem, hj'eq⟩ := Finset.exists_mem_eq_inf' hne (fun j' => |b (σ i) - b j'|)
        rw [hj'eq]
        have h1 := ps_wait_eats_nearest a b pref hp s i ji j' hji (Finset.mem_filter.mp hj'mem).2
        have h2 := abs_sub_le (a i) (b (σ i)) (b j')
        linarith
      · rw [dif_neg hm, add_zero]
        exact ps_wait_eats_nearest a b pref hp s i ji (σ i) hji (lt_of_not_ge hm)
    · intro j _ hj
      rw [if_neg (fun h => hj (ps_wait_eats_unique n pref s i j ji h hji)), zero_mul]
    · intro h; exact absurd (Finset.mem_univ _) h
  · have hz : ∀ i j, ¬ ps_wait_eats n pref s i j := fun i j h => hA ⟨j, h.1⟩
    simp only [hz, if_false, zero_mul, Finset.sum_const_zero]
    apply add_nonneg
    · exact mul_nonneg hL0 (Finset.sum_nonneg (fun i _ => abs_nonneg _))
    · apply Finset.sum_nonneg
      intro m _
      split_ifs with h
      · exact absurd h.2 (by
          rintro ⟨j, hj⟩; exact hA ⟨j, (Finset.mem_filter.mp hj).2⟩)
      · exact le_rfl

theorem probabilistic_serial_line_cost_le_add_item_wait {n : ℕ} (a b : Fin n → ℝ)
    (pref : Fin n → Equiv.Perm (Fin n)) (h : is_line_distance_preference_profile a b pref) :
    probabilistic_serial_line_cost a b pref ≤
      line_min_matching_cost a b + ∑ j, probabilistic_serial_line_item_wait b pref j := by
  classical
  have hsucc : ∀ k, probabilistic_serial_phase_state n pref (k + 1) =
      probabilistic_serial_phase n pref (probabilistic_serial_phase_state n pref k) := by
    intro k; simp [probabilistic_serial_phase_state, Function.iterate_succ_apply']
  have hnn : ∀ k, ∀ j, 0 ≤ (probabilistic_serial_phase_state n pref k).1 j := by
    intro k
    induction k with
    | zero => intro j; simp [probabilistic_serial_phase_state]
    | succ k ih =>
      intro j
      rw [hsucc]; exact (ps_wait_phase_fst_le_and_nonneg n pref _ ih j).1
  have hstep : ∀ k j, (probabilistic_serial_phase_state n pref (k + 1)).1 j ≤
      (probabilistic_serial_phase_state n pref k).1 j := by
    intro k j
    rw [hsucc]; exact (ps_wait_phase_fst_le_and_nonneg n pref _ (hnn k) j).2
  have hX : ∀ k i j, (probabilistic_serial_phase_state n pref k).2 i j =
      ∑ m ∈ Finset.range k, (if ps_wait_eats n pref (probabilistic_serial_phase_state n pref m) i j
        then ps_wait_time n pref (probabilistic_serial_phase_state n pref m) else 0) := by
    intro k
    induction k with
    | zero => intro i j; simp [probabilistic_serial_phase_state]
    | succ k ih =>
      intro i j
      rw [Finset.sum_range_succ, ← ih, hsucc, ps_wait_phase_eq]
  have hlen0 : ∀ k, 0 ≤ probabilistic_serial_phase_length n pref k := by
    intro k
    unfold probabilistic_serial_phase_length
    apply div_nonneg _ (Nat.cast_nonneg _)
    have := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hstep k j)
    linarith
  have hlenT : ∀ k, (∃ j, 0 < (probabilistic_serial_phase_state n pref k).1 j) →
      probabilistic_serial_phase_length n pref k =
        ps_wait_time n pref (probabilistic_serial_phase_state n pref k) := by
    intro k hA
    obtain ⟨j0, _⟩ := hA
    have hn : (n : ℝ) ≠ 0 := by
      have : 0 < n := Fin.pos j0
      exact_mod_cast this.ne'
    unfold probabilistic_serial_phase_length
    rw [hsucc, ps_wait_phase_eq]
    simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]
    rw [ps_wait_card_sum n pref _ ⟨j0, by assumption⟩]
    field_simp
    ring
  have hlensum : ∑ k ∈ Finset.range n, probabilistic_serial_phase_length n pref k ≤ 1 := by
    unfold probabilistic_serial_phase_length
    rw [← Finset.sum_div, Finset.sum_range_sub']
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn; simp
    · have hnr : (0 : ℝ) < n := by exact_mod_cast hn
      rw [div_le_one hnr]
      have h0 : ∑ j, (probabilistic_serial_phase_state n pref 0).1 j = n := by
        simp [probabilistic_serial_phase_state]
      have := Finset.sum_nonneg (fun j (_ : j ∈ Finset.univ) => hnn n j)
      linarith
  obtain ⟨σ, -, hσ⟩ := Finset.exists_mem_eq_inf' (Finset.univ_nonempty (α := Equiv.Perm (Fin n)))
    (fun σ : Equiv.Perm (Fin n) => ∑ i, |a i - b (σ i)|)
  have hopt : line_min_matching_cost a b = ∑ i, |a i - b (σ i)| := hσ
  have hC0 : 0 ≤ ∑ i, |a i - b (σ i)| := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  unfold probabilistic_serial_line_cost probabilistic_serial_fractional_assignment
  have hst : ((probabilistic_serial_phase n pref)^[n] (fun _ => 1, fun _ _ => 0)) =
      probabilistic_serial_phase_state n pref n := rfl
  rw [hst]
  simp_rw [hX n, Finset.sum_mul]
  conv_lhs => arg 2; ext x; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  calc _ ≤ ∑ k ∈ Finset.range n, (probabilistic_serial_phase_length n pref k * ∑ i, |a i - b (σ i)| +
        ∑ m, (if h : (probabilistic_serial_phase_state n pref k).1 m ≤ 0 ∧
          (Finset.univ.filter (fun j' => 0 < (probabilistic_serial_phase_state n pref k).1 j')).Nonempty
        then probabilistic_serial_phase_length n pref k *
          (Finset.univ.filter (fun j' => 0 < (probabilistic_serial_phase_state n pref k).1 j')).inf' h.2
            (fun j' => |b m - b j'|)
        else 0)) := by
        apply Finset.sum_le_sum
        intro k _
        exact ps_wait_phase_cost_le a b pref h _ σ _ (hlen0 k) (hlenT k)
    _ = (∑ k ∈ Finset.range n, probabilistic_serial_phase_length n pref k) * ∑ i, |a i - b (σ i)| +
        ∑ j, probabilistic_serial_line_item_wait b pref j := by
        rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_comm (s := Finset.range n)]
        rfl
    _ ≤ _ := by
        rw [hopt]
        have := mul_le_mul_of_nonneg_right hlensum hC0
        linarith
