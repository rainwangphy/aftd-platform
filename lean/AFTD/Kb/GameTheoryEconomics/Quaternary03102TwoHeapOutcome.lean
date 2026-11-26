import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Quaternary03102MisereOutcome
import AFTD.Kb.GameTheoryEconomics.MisereOutcome
import AFTD.Kb.GameTheoryEconomics.Quaternary03102HeapOptions
import AFTD.Kb.GameTheoryEconomics.Quaternary03102Options
import AFTD.Kb.GameTheoryEconomics.Quaternary03102MisereOutcomeComp

/-!
# quaternary_03102_two_heap_outcome

Topic: combinatorial_games   Node: 3dc78abba39a

Provenance: formalization of a published result. Source: arXiv:2611.29198 Theorem 3.1

In the quaternary game 0.3102, for all heap sizes x, y ≥ 3, the two-heap misère outcome is P if and only if the absolute difference |y - x| is congruent to 0 or 3 modulo 5.
-/

/-- Closed form of the P-positions of the two-heap misère game 0.3102. -/
def quaternary_03102_two_heap_P_form (x y : ℕ) : Prop :=
  (x = 0 ∧ (y % 5 = 1 ∨ y % 5 = 3)) ∨ (y = 0 ∧ (x % 5 = 1 ∨ x % 5 = 3)) ∨
  (x = 1 ∧ 4 ≤ y ∧ (y % 5 = 2 ∨ y % 5 = 4)) ∨ (y = 1 ∧ 4 ≤ x ∧ (x % 5 = 2 ∨ x % 5 = 4)) ∨
  (x = 2 ∧ (y = 2 ∨ (5 ≤ y ∧ y % 5 = 0))) ∨ (y = 2 ∧ 5 ≤ x ∧ x % 5 = 0) ∨
  (3 ≤ x ∧ 3 ≤ y ∧ ((y ≤ x ∧ ((x - y) % 5 = 0 ∨ (x - y) % 5 = 3)) ∨
    (x < y ∧ ((y - x) % 5 = 0 ∨ (y - x) % 5 = 3))))

theorem quaternary_03102_two_heap_P_form_big (x y : ℕ) (hx : 3 ≤ x) (hy : 3 ≤ y) :
    quaternary_03102_two_heap_P_form x y ↔
      ((y ≤ x ∧ ((x - y) % 5 = 0 ∨ (x - y) % 5 = 3)) ∨
        (x < y ∧ ((y - x) % 5 = 0 ∨ (y - x) % 5 = 3))) := by
  unfold quaternary_03102_two_heap_P_form
  constructor
  · intro h; omega
  · intro h; right; right; right; right; right; right; exact ⟨hx, hy, h⟩

set_option maxHeartbeats 2000000 in
theorem quaternary_03102_two_heap_P_form_local_smallx (x y : ℕ) (hx : x ≤ 6) :
    quaternary_03102_two_heap_P_form x y ↔
      ¬ (x = 0 ∧ y = 0) ∧
      ¬ (((x = 1 ∨ x = 2) ∧ quaternary_03102_two_heap_P_form 0 y) ∨
         (1 < x ∧ quaternary_03102_two_heap_P_form (x - 1) y) ∨
         (4 < x ∧ quaternary_03102_two_heap_P_form (x - 4) y) ∨
         ((y = 1 ∨ y = 2) ∧ quaternary_03102_two_heap_P_form x 0) ∨
         (1 < y ∧ quaternary_03102_two_heap_P_form x (y - 1)) ∨
         (4 < y ∧ quaternary_03102_two_heap_P_form x (y - 4))) := by
  interval_cases x <;> simp only [quaternary_03102_two_heap_P_form] <;> norm_num <;> omega

theorem quaternary_03102_two_heap_P_form_local_smally (x y : ℕ) (hy : y ≤ 6) :
    quaternary_03102_two_heap_P_form x y ↔
      ¬ (x = 0 ∧ y = 0) ∧
      ¬ (((x = 1 ∨ x = 2) ∧ quaternary_03102_two_heap_P_form 0 y) ∨
         (1 < x ∧ quaternary_03102_two_heap_P_form (x - 1) y) ∨
         (4 < x ∧ quaternary_03102_two_heap_P_form (x - 4) y) ∨
         ((y = 1 ∨ y = 2) ∧ quaternary_03102_two_heap_P_form x 0) ∨
         (1 < y ∧ quaternary_03102_two_heap_P_form x (y - 1)) ∨
         (4 < y ∧ quaternary_03102_two_heap_P_form x (y - 4))) := by
  interval_cases y <;> simp only [quaternary_03102_two_heap_P_form] <;> norm_num <;> omega

theorem quaternary_03102_two_heap_P_form_local (x y : ℕ) :
    quaternary_03102_two_heap_P_form x y ↔
      ¬ (x = 0 ∧ y = 0) ∧
      ¬ (((x = 1 ∨ x = 2) ∧ quaternary_03102_two_heap_P_form 0 y) ∨
         (1 < x ∧ quaternary_03102_two_heap_P_form (x - 1) y) ∨
         (4 < x ∧ quaternary_03102_two_heap_P_form (x - 4) y) ∨
         ((y = 1 ∨ y = 2) ∧ quaternary_03102_two_heap_P_form x 0) ∨
         (1 < y ∧ quaternary_03102_two_heap_P_form x (y - 1)) ∨
         (4 < y ∧ quaternary_03102_two_heap_P_form x (y - 4))) := by
  rcases Nat.lt_or_ge x 7 with hx | hx
  · exact quaternary_03102_two_heap_P_form_local_smallx x y (by omega)
  rcases Nat.lt_or_ge y 7 with hy | hy
  · exact quaternary_03102_two_heap_P_form_local_smally x y (by omega)
  rw [quaternary_03102_two_heap_P_form_big x y (by omega) (by omega),
    quaternary_03102_two_heap_P_form_big (x - 1) y (by omega) (by omega),
    quaternary_03102_two_heap_P_form_big (x - 4) y (by omega) (by omega),
    quaternary_03102_two_heap_P_form_big x (y - 1) (by omega) (by omega),
    quaternary_03102_two_heap_P_form_big x (y - 4) (by omega) (by omega)]
  have h1 : ¬ (x = 1 ∨ x = 2) := by omega
  have h2 : ¬ (y = 1 ∨ y = 2) := by omega
  simp only [h1, h2, false_and, false_or]
  omega

theorem quaternary_03102_heap_options_mem (h a : ℕ) :
    a ∈ quaternary_03102_heap_options h ↔
      ((h = 1 ∨ h = 2) ∧ a = 0) ∨ (1 < h ∧ a = h - 1) ∨ (4 < h ∧ a = h - 4) := by
  unfold quaternary_03102_heap_options
  split_ifs <;> simp_all <;> omega

theorem quaternary_03102_comp_P_iff (n : ℕ) : ∀ x y, x + y ≤ n →
    (quaternary_03102_misere_outcome_comp n x y = MisereOutcome.P ↔
      quaternary_03102_two_heap_P_form x y) := by
  induction n with
  | zero =>
    intro x y hxy
    have hx : x = 0 := by omega
    have hy : y = 0 := by omega
    subst hx hy
    simp [quaternary_03102_misere_outcome_comp, quaternary_03102_two_heap_P_form]
  | succ n ih =>
    intro x y hxy
    have hopt : (∃ p ∈ quaternary_03102_options x y,
        quaternary_03102_misere_outcome_comp n p.1 p.2 = MisereOutcome.P) ↔
        (((x = 1 ∨ x = 2) ∧ quaternary_03102_two_heap_P_form 0 y) ∨
         (1 < x ∧ quaternary_03102_two_heap_P_form (x - 1) y) ∨
         (4 < x ∧ quaternary_03102_two_heap_P_form (x - 4) y) ∨
         ((y = 1 ∨ y = 2) ∧ quaternary_03102_two_heap_P_form x 0) ∨
         (1 < y ∧ quaternary_03102_two_heap_P_form x (y - 1)) ∨
         (4 < y ∧ quaternary_03102_two_heap_P_form x (y - 4))) := by
      constructor
      · rintro ⟨⟨a, b⟩, hp, hP⟩
        simp only [quaternary_03102_options, Finset.mem_union, Finset.mem_image,
          Prod.mk.injEq] at hp
        rcases hp with ⟨a', ha', rfl, rfl⟩ | ⟨b', hb', rfl, rfl⟩
        · rw [quaternary_03102_heap_options_mem] at ha'
          rcases ha' with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩
          · exact Or.inl ⟨h1, (ih _ _ (by omega)).1 hP⟩
          · exact Or.inr (Or.inl ⟨h1, (ih _ _ (by omega)).1 hP⟩)
          · exact Or.inr (Or.inr (Or.inl ⟨h1, (ih _ _ (by omega)).1 hP⟩))
        · rw [quaternary_03102_heap_options_mem] at hb'
          rcases hb' with ⟨h1, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩
          · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, (ih _ _ (by omega)).1 hP⟩)))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨h1, (ih _ _ (by omega)).1 hP⟩))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h1, (ih _ _ (by omega)).1 hP⟩))))
      · have mx : ∀ a, a ∈ quaternary_03102_heap_options x → (a, y) ∈ quaternary_03102_options x y :=
          fun a ha => by
            simp only [quaternary_03102_options, Finset.mem_union, Finset.mem_image]
            exact Or.inl ⟨a, ha, rfl⟩
        have my : ∀ b, b ∈ quaternary_03102_heap_options y → (x, b) ∈ quaternary_03102_options x y :=
          fun b hb => by
            simp only [quaternary_03102_options, Finset.mem_union, Finset.mem_image]
            exact Or.inr ⟨b, hb, rfl⟩
        rintro (⟨h1, hQ⟩ | ⟨h1, hQ⟩ | ⟨h1, hQ⟩ | ⟨h1, hQ⟩ | ⟨h1, hQ⟩ | ⟨h1, hQ⟩)
        · exact ⟨(0, y), mx 0 ((quaternary_03102_heap_options_mem _ _).2 (Or.inl ⟨h1, rfl⟩)),
            (ih _ _ (by omega)).2 hQ⟩
        · exact ⟨(x - 1, y), mx _ ((quaternary_03102_heap_options_mem _ _).2
            (Or.inr (Or.inl ⟨h1, rfl⟩))), (ih _ _ (by omega)).2 hQ⟩
        · exact ⟨(x - 4, y), mx _ ((quaternary_03102_heap_options_mem _ _).2
            (Or.inr (Or.inr ⟨h1, rfl⟩))), (ih _ _ (by omega)).2 hQ⟩
        · exact ⟨(x, 0), my 0 ((quaternary_03102_heap_options_mem _ _).2 (Or.inl ⟨h1, rfl⟩)),
            (ih _ _ (by omega)).2 hQ⟩
        · exact ⟨(x, y - 1), my _ ((quaternary_03102_heap_options_mem _ _).2
            (Or.inr (Or.inl ⟨h1, rfl⟩))), (ih _ _ (by omega)).2 hQ⟩
        · exact ⟨(x, y - 4), my _ ((quaternary_03102_heap_options_mem _ _).2
            (Or.inr (Or.inr ⟨h1, rfl⟩))), (ih _ _ (by omega)).2 hQ⟩
    rw [quaternary_03102_two_heap_P_form_local, ← hopt]
    simp only [quaternary_03102_misere_outcome_comp]
    split_ifs with h1 h2
    · simp [h1]
    · simp [h1, h2]
    · simp [h1, h2]

/-- Characterization of the two-heap misère outcome in 0.3102 for heaps of size at least 3. -/
theorem quaternary_03102_two_heap_outcome (x y : ℕ) (hx : 3 ≤ x) (hy : 3 ≤ y) :
    quaternary_03102_misere_outcome x y = MisereOutcome.P ↔
      Nat.dist x y % 5 = 0 ∨ Nat.dist x y % 5 = 3 := by
  unfold quaternary_03102_misere_outcome
  rw [quaternary_03102_comp_P_iff (x + y) x y le_rfl]
  unfold quaternary_03102_two_heap_P_form Nat.dist
  omega
