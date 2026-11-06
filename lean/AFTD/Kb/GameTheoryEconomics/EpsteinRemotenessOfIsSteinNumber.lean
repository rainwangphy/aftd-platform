import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EpsteinRemoteness
import AFTD.Kb.GameTheoryEconomics.IsSteinNumber
import AFTD.Kb.GameTheoryEconomics.EpsteinRemotenessLevel
import AFTD.Kb.GameTheoryEconomics.EpsteinUp
import AFTD.Kb.GameTheoryEconomics.EpsteinDown

/-!
# epstein_remoteness_of_is_stein_number

Topic: combinatorial_games   Node: ba659febe67e

Provenance: formalization of a published result. Source: arXiv:2611.05898 Def 1.3

For every natural number n, if n is an E. P. Stein number (is_stein_number n), then its remoteness epstein_remoteness n is equal to 2.
-/

/-- The remoteness level 1 of Epstein's game is exactly the set of nonzero positions whose down- or up-move lands on 0. -/
lemma epstein_remoteness_of_is_stein_number_level_one_eq :
    epstein_remoteness_level 1 = {n : ℕ | n ≠ 0 ∧ (epstein_down n = 0 ∨ epstein_up n = 0)} := by
  rw [epstein_remoteness_level.eq_def 1]
  dsimp only
  rw [epstein_remoteness_level.eq_1]
  simp

/-- The remoteness level 2 of Epstein's game is exactly the set of nonzero positions both of whose moves land in level 1. -/
lemma epstein_remoteness_of_is_stein_number_level_two_eq :
    epstein_remoteness_level 2 = {n : ℕ | n ≠ 0 ∧ epstein_down n ∈ epstein_remoteness_level 1 ∧ epstein_up n ∈ epstein_remoteness_level 1} := by
  rw [epstein_remoteness_level.eq_def 2]
  dsimp only
  simp only [Set.mem_iUnion, exists_prop]
  ext n
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨h0, h1, h2, _⟩
    refine ⟨h0, ?_, ?_⟩
    · obtain ⟨i, hi, hmem⟩ := h1
      interval_cases i
      simpa using hmem
    · obtain ⟨i, hi, hmem⟩ := h2
      interval_cases i
      simpa using hmem
  · rintro ⟨h0, h1, h2⟩
    exact ⟨h0, ⟨0, le_refl 0, h1⟩, ⟨0, le_refl 0, h2⟩, Or.inl h1⟩

/-- Every positive perfect square lies in remoteness level 1 of Epstein's game. -/
lemma epstein_remoteness_of_is_stein_number_pos_square_mem_level_one {x : ℕ} (hx : 0 < x) (hsq : IsSquare x) :
    x ∈ epstein_remoteness_level 1 := by
  rw [epstein_remoteness_of_is_stein_number_level_one_eq]
  refine ⟨hx.ne', Or.inl ?_⟩
  obtain ⟨r, rfl⟩ := hsq
  simp [epstein_down, Nat.sqrt_eq, pow_two]

/-- Every E. P. Stein number has remoteness 2 in Epstein's game. -/
theorem epstein_remoteness_of_is_stein_number (n : ℕ) (h : is_stein_number n) : epstein_remoteness n = 2 := by
  classical
  have hn0 : 0 < n := h.1
  have hd0 : 0 < epstein_down n := h.2.1
  have hdsq : IsSquare (epstein_down n) := h.2.2.1
  have hu0 : 0 < epstein_up n := h.2.2.2.1
  have husq : IsSquare (epstein_up n) := h.2.2.2.2
  have hdlvl : epstein_down n ∈ epstein_remoteness_level 1 :=
    epstein_remoteness_of_is_stein_number_pos_square_mem_level_one hd0 hdsq
  have hulvl : epstein_up n ∈ epstein_remoteness_level 1 :=
    epstein_remoteness_of_is_stein_number_pos_square_mem_level_one hu0 husq
  have hmem2 : n ∈ epstein_remoteness_level 2 := by
    rw [epstein_remoteness_of_is_stein_number_level_two_eq]
    exact ⟨hn0.ne', hdlvl, hulvl⟩
  have hn0lvl : n ∉ epstein_remoteness_level 0 := by
    rw [epstein_remoteness_level.eq_1]
    simp [hn0.ne']
  have hn1lvl : n ∉ epstein_remoteness_level 1 := by
    rw [epstein_remoteness_of_is_stein_number_level_one_eq]
    simp [hd0.ne', hu0.ne']
  have hex : ∃ k, n ∈ epstein_remoteness_level k := ⟨2, hmem2⟩
  have hstep : epstein_remoteness n = (some (Nat.find hex) : WithTop ℕ) := by
    rw [epstein_remoteness.eq_def]
    exact @dif_pos (c := ∃ k, n ∈ epstein_remoteness_level k) (h := Classical.propDecidable _) hex
      (α := WithTop ℕ) (t := fun hh => @Option.some ℕ (Nat.find (p := fun k => n ∈ epstein_remoteness_level k) hh))
      (e := fun _ => ⊤)
  have hfind : Nat.find hex = 2 := by
    have hspec : n ∈ epstein_remoteness_level (Nat.find hex) := Nat.find_spec hex
    have hle : Nat.find hex ≤ 2 := Nat.find_min' hex hmem2
    have hne0 : Nat.find hex ≠ 0 := by
      intro hh
      exact hn0lvl (hh ▸ hspec)
    have hne1 : Nat.find hex ≠ 1 := by
      intro hh
      exact hn1lvl (hh ▸ hspec)
    omega
  rw [hstep, hfind]
  rfl
