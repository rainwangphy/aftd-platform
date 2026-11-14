import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PyranimCollisionProb
import AFTD.Kb.GameTheoryEconomics.PyranimFullPyramid
import AFTD.Kb.GameTheoryEconomics.PyranimOptions
import AFTD.Kb.GameTheoryEconomics.PyranimStablePositions
import AFTD.Kb.GameTheoryEconomics.PyranimGameIso
import AFTD.Kb.GameTheoryEconomics.PyranimIsOrderIdeal

/-!
# pyranim_collision_prob_one

Topic: combinatorial_games   Node: eb08b7261973

Provenance: formalization of a published result. Source: arXiv:2611.16153 Sec. 5.3, Question 4

The collision probability pyranim_collision_prob 1 for a 1-tier pyramid game is equal to 1 / 2.
-/

lemma pyranim_collision_prob_one_game_iso_refl (X : Finset (ℕ × ℕ)) : pyranim_game_iso X X := by
  use (fun A B => A = B)
  refine ⟨rfl, ?_⟩
  intro A B h
  subst h
  refine ⟨Equiv.refl _, ?_⟩
  intro o
  rfl

lemma pyranim_collision_prob_one_not_game_iso_empty_singleton : ¬ pyranim_game_iso ∅ {(1, 1)} := by
  intro ⟨R, hR, hstep⟩
  rcases hstep ∅ {(1, 1)} hR with ⟨f, hf⟩
  have h1 : IsEmpty (pyranim_options (∅ : Finset (ℕ × ℕ))) := by
    rw [show pyranim_options (∅ : Finset (ℕ × ℕ)) = ∅ by decide]
    infer_instance
  have h2 : Nonempty (pyranim_options ({(1, 1)} : Finset (ℕ × ℕ))) := by
    rw [show pyranim_options ({(1, 1)} : Finset (ℕ × ℕ)) = {∅} by decide]
    exact ⟨⟨∅, Finset.mem_singleton_self ∅⟩⟩
  exact IsEmpty.false (f.symm h2.some)

lemma pyranim_collision_prob_one_not_game_iso_singleton_empty : ¬ pyranim_game_iso {(1, 1)} ∅ := by
  intro ⟨R, hR, hstep⟩
  rcases hstep {(1, 1)} ∅ hR with ⟨f, hf⟩
  have h1 : IsEmpty (pyranim_options (∅ : Finset (ℕ × ℕ))) := by
    rw [show pyranim_options (∅ : Finset (ℕ × ℕ)) = ∅ by decide]
    infer_instance
  have h2 : Nonempty (pyranim_options ({(1, 1)} : Finset (ℕ × ℕ))) := by
    rw [show pyranim_options ({(1, 1)} : Finset (ℕ × ℕ)) = {∅} by decide]
    exact ⟨⟨∅, Finset.mem_singleton_self ∅⟩⟩
  exact IsEmpty.false (f h2.some)

lemma pyranim_collision_prob_one_filter_iso_eq :
    (@Finset.filter (Finset (ℕ × ℕ) × Finset (ℕ × ℕ)) (fun ⟨X, Y⟩ => pyranim_game_iso X Y)
      (fun _ => Classical.propDecidable _) ({∅, {(1, 1)}} ×ˢ {∅, {(1, 1)}})) =
    {(∅, ∅), ({(1, 1)}, {(1, 1)})} := by
  ext ⟨X, Y⟩
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  constructor
  · rintro ⟨⟨rfl | rfl, rfl | rfl⟩, h_iso⟩
    · left; exact ⟨rfl, rfl⟩
    · exact False.elim (pyranim_collision_prob_one_not_game_iso_empty_singleton h_iso)
    · exact False.elim (pyranim_collision_prob_one_not_game_iso_singleton_empty h_iso)
    · right; exact ⟨rfl, rfl⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨by simp, pyranim_collision_prob_one_game_iso_refl ∅⟩
    · exact ⟨by simp, pyranim_collision_prob_one_game_iso_refl {(1, 1)}⟩

/-- The game-isomorphism collision probability for 1-tier Pyranim is 1/2. -/
theorem pyranim_collision_prob_one : pyranim_collision_prob 1 = 1 / 2 := by
  dsimp [pyranim_collision_prob]
  have hT : pyranim_stable_positions 1 = {∅, {(1, 1)}} := by
    dsimp [pyranim_stable_positions]
    have h_pyr : pyranim_full_pyramid 1 = {(1, 1)} := by decide
    rw [h_pyr]
    ext X
    simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_insert, Finset.mem_singleton]
    constructor
    · rintro ⟨hsub, _⟩
      rw [Finset.subset_singleton_iff] at hsub
      exact hsub
    · rintro (rfl | rfl)
      · refine ⟨by simp, ?_⟩
        intro p hp
        simp at hp
      · refine ⟨by simp, ?_⟩
        intro p hp a ha b hb
        simp only [Finset.mem_singleton] at hp
        subst hp
        simp only [Finset.mem_Icc] at ha hb
        have ha1 : a = 1 := by omega
        have hb1 : b = 1 := by omega
        subst ha1 hb1
        simp
  rw [hT]
  rw [pyranim_collision_prob_one_filter_iso_eq]
  have h_card_num : ({(∅, ∅), ({(1, 1)}, {(1, 1)})} : Finset (Finset (ℕ × ℕ) × Finset (ℕ × ℕ))).card = 2 := by decide
  have h_card_den : ({∅, {(1, 1)}} : Finset (Finset (ℕ × ℕ))).card = 2 := by decide
  rw [h_card_num, h_card_den]
  norm_num
