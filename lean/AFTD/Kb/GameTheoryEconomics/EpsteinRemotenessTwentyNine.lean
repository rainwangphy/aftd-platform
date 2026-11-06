import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EpsteinRemoteness
import AFTD.Kb.GameTheoryEconomics.EpsteinRemotenessLevel
import AFTD.Kb.GameTheoryEconomics.EpsteinDown
import AFTD.Kb.GameTheoryEconomics.EpsteinRemotenessOfIsSteinNumber
import AFTD.Kb.GameTheoryEconomics.EpsteinUp

/-!
# epstein_remoteness_twenty_nine

Topic: combinatorial_games   Node: f665e7f5f07c

Provenance: formalization of a published result. Source: arXiv:2611.05898 Ex 1.4

In Epstein's put-or-take-a-square game, the natural number 29 has remoteness epstein_remoteness 29 = 4.
-/

lemma epstein_remoteness_twenty_nine_level_three :
    epstein_remoteness_level 3 = {n | n ≠ 0 ∧
      (epstein_down n ∈ epstein_remoteness_level 2 ∨ epstein_up n ∈ epstein_remoteness_level 2) ∧
      epstein_down n ≠ 0 ∧ epstein_up n ≠ 0} := by
  have h := epstein_remoteness_level.eq_2 2
  rw [h]
  dsimp
  ext n
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hn, h2, hj⟩
    have h0 := hj 0 (by decide)
    rw [MulZeroClass.mul_zero, epstein_remoteness_level.eq_1, Set.mem_singleton_iff] at h0
    exact ⟨hn, h2, h0.1, h0.2⟩
  · rintro ⟨hn, h2, hd0, hu0⟩
    refine ⟨hn, h2, fun j hj => ?_⟩
    interval_cases j
    rw [MulZeroClass.mul_zero, epstein_remoteness_level.eq_1, Set.mem_singleton_iff]
    exact ⟨hd0, hu0⟩

lemma epstein_remoteness_twenty_nine_level_four :
    epstein_remoteness_level 4 = {n | n ≠ 0 ∧
      epstein_down n ∈ epstein_remoteness_level 1 ∪ epstein_remoteness_level 3 ∧
      epstein_up n ∈ epstein_remoteness_level 1 ∪ epstein_remoteness_level 3 ∧
      (epstein_down n ∈ epstein_remoteness_level 3 ∨ epstein_up n ∈ epstein_remoteness_level 3)} := by
  have h := epstein_remoteness_level.eq_2 3
  rw [h]
  dsimp
  ext n
  simp only [Set.mem_iUnion, exists_prop, Set.mem_union, Set.mem_ofPred_eq]
  constructor
  · rintro ⟨hn, ⟨j1, hj1, hd⟩, ⟨j2, hj2, hu⟩, h3⟩
    refine ⟨hn, ?_, ?_, h3⟩
    · interval_cases j1 <;> [left; right] <;> assumption
    · interval_cases j2 <;> [left; right] <;> assumption
  · rintro ⟨hn, hd, hu, h3⟩
    refine ⟨hn, ?_, ?_, h3⟩
    · rcases hd with hd | hd
      · exact ⟨0, Nat.zero_le 1, hd⟩
      · exact ⟨1, le_refl 1, hd⟩
    · rcases hu with hu | hu
      · exact ⟨0, Nat.zero_le 1, hu⟩
      · exact ⟨1, le_refl 1, hu⟩

lemma epstein_remoteness_twenty_nine_mem_level_one_four : 4 ∈ epstein_remoteness_level 1 := by
  rw [epstein_remoteness_of_is_stein_number_level_one_eq]
  refine ⟨by decide, Or.inl ?_⟩
  norm_num [epstein_down]

lemma epstein_remoteness_twenty_nine_mem_level_one_one : 1 ∈ epstein_remoteness_level 1 := by
  rw [epstein_remoteness_of_is_stein_number_level_one_eq]
  refine ⟨by decide, Or.inl ?_⟩
  norm_num [epstein_down]

lemma epstein_remoteness_twenty_nine_mem_level_one_nine : 9 ∈ epstein_remoteness_level 1 := by
  rw [epstein_remoteness_of_is_stein_number_level_one_eq]
  refine ⟨by decide, Or.inl ?_⟩
  norm_num [epstein_down]

lemma epstein_remoteness_twenty_nine_mem_level_two_five : 5 ∈ epstein_remoteness_level 2 := by
  rw [epstein_remoteness_of_is_stein_number_level_two_eq]
  refine ⟨by decide, ?_, ?_⟩
  · have : epstein_down 5 = 1 := by norm_num [epstein_down]
    rw [this]
    exact epstein_remoteness_twenty_nine_mem_level_one_one
  · have : epstein_up 5 = 9 := by norm_num [epstein_up]
    rw [this]
    exact epstein_remoteness_twenty_nine_mem_level_one_nine

lemma epstein_remoteness_twenty_nine_mem_level_three_fifty_four : 54 ∈ epstein_remoteness_level 3 := by
  rw [epstein_remoteness_twenty_nine_level_three]
  refine ⟨by decide, Or.inl ?_, ?_, ?_⟩
  · have : epstein_down 54 = 5 := by norm_num [epstein_down]
    rw [this]
    exact epstein_remoteness_twenty_nine_mem_level_two_five
  · intro h
    have : epstein_down 54 = 5 := by norm_num [epstein_down]
    rw [this] at h
    revert h; decide
  · intro h
    have : epstein_up 54 = 103 := by norm_num [epstein_up]
    rw [this] at h
    revert h; decide

lemma epstein_remoteness_twenty_nine_mem_level_four_twenty_nine : 29 ∈ epstein_remoteness_level 4 := by
  rw [epstein_remoteness_twenty_nine_level_four]
  refine ⟨by decide, ?_, ?_, ?_⟩
  · have hd : epstein_down 29 = 4 := by norm_num [epstein_down]
    rw [hd]
    exact Or.inl epstein_remoteness_twenty_nine_mem_level_one_four
  · have hu : epstein_up 29 = 54 := by norm_num [epstein_up]
    rw [hu]
    exact Or.inr epstein_remoteness_twenty_nine_mem_level_three_fifty_four
  · have hu : epstein_up 29 = 54 := by norm_num [epstein_up]
    rw [hu]
    exact Or.inr epstein_remoteness_twenty_nine_mem_level_three_fifty_four

lemma epstein_remoteness_twenty_nine_not_mem_level_one_zero : 0 ∉ epstein_remoteness_level 1 := by
  rw [epstein_remoteness_of_is_stein_number_level_one_eq]
  simp

lemma epstein_remoteness_twenty_nine_not_mem_level_one_five : 5 ∉ epstein_remoteness_level 1 := by
  rw [epstein_remoteness_of_is_stein_number_level_one_eq]
  rintro ⟨-, h | h⟩
  · have : epstein_down 5 = 1 := by norm_num [epstein_down]
    omega
  · have : epstein_up 5 = 9 := by norm_num [epstein_up]
    omega

lemma epstein_remoteness_twenty_nine_not_mem_level_one_fifty_four : 54 ∉ epstein_remoteness_level 1 := by
  rw [epstein_remoteness_of_is_stein_number_level_one_eq]
  rintro ⟨-, h | h⟩
  · have : epstein_down 54 = 5 := by norm_num [epstein_down]
    omega
  · have : epstein_up 54 = 103 := by norm_num [epstein_up]
    omega

lemma epstein_remoteness_twenty_nine_not_mem_level_two_four : 4 ∉ epstein_remoteness_level 2 := by
  rw [epstein_remoteness_of_is_stein_number_level_two_eq]
  rintro ⟨-, hd, -⟩
  have : epstein_down 4 = 0 := by norm_num [epstein_down]
  rw [this] at hd
  exact epstein_remoteness_twenty_nine_not_mem_level_one_zero hd

lemma epstein_remoteness_twenty_nine_not_mem_level_two_fifty_four : 54 ∉ epstein_remoteness_level 2 := by
  rw [epstein_remoteness_of_is_stein_number_level_two_eq]
  rintro ⟨-, hd, -⟩
  have : epstein_down 54 = 5 := by norm_num [epstein_down]
  rw [this] at hd
  exact epstein_remoteness_twenty_nine_not_mem_level_one_five hd

lemma epstein_remoteness_twenty_nine_not_mem_level_zero_twenty_nine : 29 ∉ epstein_remoteness_level 0 := by
  rw [epstein_remoteness_level.eq_1]
  simp

lemma epstein_remoteness_twenty_nine_not_mem_level_one_twenty_nine : 29 ∉ epstein_remoteness_level 1 := by
  rw [epstein_remoteness_of_is_stein_number_level_one_eq]
  rintro ⟨-, h | h⟩
  · have : epstein_down 29 = 4 := by norm_num [epstein_down]
    omega
  · have : epstein_up 29 = 54 := by norm_num [epstein_up]
    omega

lemma epstein_remoteness_twenty_nine_not_mem_level_two_twenty_nine : 29 ∉ epstein_remoteness_level 2 := by
  rw [epstein_remoteness_of_is_stein_number_level_two_eq]
  rintro ⟨-, -, hu⟩
  have : epstein_up 29 = 54 := by norm_num [epstein_up]
  rw [this] at hu
  exact epstein_remoteness_twenty_nine_not_mem_level_one_fifty_four hu

lemma epstein_remoteness_twenty_nine_not_mem_level_three_twenty_nine : 29 ∉ epstein_remoteness_level 3 := by
  rw [epstein_remoteness_twenty_nine_level_three]
  rintro ⟨-, h | h, -, -⟩
  · have : epstein_down 29 = 4 := by norm_num [epstein_down]
    rw [this] at h
    exact epstein_remoteness_twenty_nine_not_mem_level_two_four h
  · have : epstein_up 29 = 54 := by norm_num [epstein_up]
    rw [this] at h
    exact epstein_remoteness_twenty_nine_not_mem_level_two_fifty_four h

/-- The integer 29 has remoteness 4 in Epstein's put-or-take-a-square game. -/
theorem epstein_remoteness_twenty_nine : epstein_remoteness 29 = 4 := by
  classical
  have hex : ∃ k, 29 ∈ epstein_remoteness_level k := ⟨4, epstein_remoteness_twenty_nine_mem_level_four_twenty_nine⟩
  have hstep : epstein_remoteness 29 = (some (Nat.find hex) : WithTop ℕ) := by
    rw [epstein_remoteness.eq_def]
    exact @dif_pos (c := ∃ k, 29 ∈ epstein_remoteness_level k) (h := Classical.propDecidable _) hex
      (α := WithTop ℕ) (t := fun hh => @Option.some ℕ (Nat.find (p := fun k => 29 ∈ epstein_remoteness_level k) hh))
      (e := fun _ => ⊤)
  have hfind : Nat.find hex = 4 := by
    have hspec : 29 ∈ epstein_remoteness_level (Nat.find hex) := Nat.find_spec hex
    have hle : Nat.find hex ≤ 4 := Nat.find_min' hex epstein_remoteness_twenty_nine_mem_level_four_twenty_nine
    interval_cases Nat.find hex
    · exact False.elim (epstein_remoteness_twenty_nine_not_mem_level_zero_twenty_nine hspec)
    · exact False.elim (epstein_remoteness_twenty_nine_not_mem_level_one_twenty_nine hspec)
    · exact False.elim (epstein_remoteness_twenty_nine_not_mem_level_two_twenty_nine hspec)
    · exact False.elim (epstein_remoteness_twenty_nine_not_mem_level_three_twenty_nine hspec)
    · rfl
  rw [hstep, hfind]
  rfl
