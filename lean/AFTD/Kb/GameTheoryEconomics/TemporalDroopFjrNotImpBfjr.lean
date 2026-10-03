import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TemporalSat
import AFTD.Kb.GameTheoryEconomics.IsTemporalDroopFjr
import AFTD.Kb.GameTheoryEconomics.TemporalEmbedSat
import AFTD.Kb.GameTheoryEconomics.IsBfjrCohesive
import AFTD.Kb.GameTheoryEconomics.IsTemporalBfjr
import AFTD.Kb.GameTheoryEconomics.TfjrBallot
import AFTD.Kb.GameTheoryEconomics.TfjrCount
import AFTD.Kb.GameTheoryEconomics.TfjrAvoid
import AFTD.Kb.GameTheoryEconomics.TfjrDroopLe

/-!
# temporal_droop_fjr_not_imp_bfjr

Topic: social_choice   Node: 05826c7fc003

Droop-FJR does not imply BFJR in temporal voting, even when no voter approves every candidate in a round. Four voters, six rounds, two candidates: the outcome choosing candidate 1 in every round provides Droop-FJR, but S = {0, 1} is (2, 1)-BFJR-cohesive and gets satisfaction 0. This answers the question left open in arXiv:2505.22513, App. A.3.
-/

/-- Droop-FJR does not imply BFJR in temporal voting, even when no voter approves every candidate in a round. Four voters, six rounds, two candidates: the outcome choosing candidate 1 in every round provides Droop-FJR, but S = {0, 1} is (2, 1)-BFJR-cohesive and gets satisfaction 0. This answers the question left open in arXiv:2505.22513, App. A.3. -/
theorem temporal_droop_fjr_not_imp_bfjr :
    ∃ a : Fin 4 → Fin 6 → Finset (Fin 2), ∃ o : Fin 6 → Fin 2,
      (∀ i r, a i r ≠ Finset.univ) ∧ is_temporal_droop_fjr a o ∧ ¬ is_temporal_bfjr a o := by
  refine ⟨tfjr_ballot, fun _ => 1, by decide, ?_, ?_⟩
  · intro S hS T
    rcases tfjr_count S T hS with ⟨i, hi, hi2⟩ | ⟨j, hj, hcard⟩
    · obtain ⟨R, hRT, hR⟩ := Finset.exists_subset_card_eq
        (tfjr_droop_le T.card S.card 4 (by simpa using Finset.card_le_univ S))
      refine ⟨R, hRT, hR, fun o' => ⟨i, hi, i, hi, ?_⟩⟩
      have h6 : ∀ i : Fin 4, 2 ≤ i.val →
          temporal_sat tfjr_ballot i (fun _ => 1) Finset.univ = 6 := by decide
      rw [h6 i hi2]
      calc temporal_sat tfjr_ballot i o' R ≤ R.card := Finset.card_filter_le _ _
        _ ≤ (Finset.univ : Finset (Fin 6)).card := Finset.card_le_univ R
        _ = 6 := by simp
    · obtain ⟨R, hRT, hR⟩ := Finset.exists_subset_card_eq hcard
      refine ⟨R, hRT.trans (Finset.filter_subset _ _), hR, fun o' => ⟨j, hj, j, hj, ?_⟩⟩
      have : temporal_sat tfjr_ballot j o' R = 0 := by
        unfold temporal_sat
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro r hr
        have := (Finset.mem_filter.1 (hRT hr)).2
        rw [this]; exact Finset.notMem_empty _
      rw [this]; exact Nat.zero_le _
  · intro h
    have hcoh : is_bfjr_cohesive tfjr_ballot {0, 1} 2 1 := by
      intro X hX
      by_cases hbig : 2 * 4 < ({0, 1} : Finset (Fin 4)).card * (X.card + 2)
      · exact Or.inr hbig
      left
      have h2 : ({0, 1} : Finset (Fin 4)).card = 2 := by decide
      rw [h2] at hbig
      have hX2 : (X.image Prod.snd).card ≤ 2 := by
        have := Finset.card_image_le (s := X) (f := Prod.snd); omega
      obtain ⟨r₁, r₂, h1, h2, h1D, h2D⟩ := tfjr_avoid _ hX2
      have hne : r₁ ≠ r₂ := by intro h; rw [h] at h1; omega
      refine ⟨{(0, r₁), (0, r₂)}, ?_, ?_, ?_⟩
      · rw [Finset.card_pair]; intro h; exact hne (Prod.ext_iff.1 h).2
      · intro i hi
        unfold temporal_embed_sat
        apply Finset.card_pos.2
        rcases Finset.mem_insert.1 hi with rfl | hi
        · refine ⟨(0, r₁), ?_⟩
          simp [tfjr_ballot, h1]
        · rw [Finset.mem_singleton] at hi; subst hi
          refine ⟨(0, r₂), ?_⟩
          have : ¬ r₂.val < 3 := by omega
          simp [tfjr_ballot, h2]
      · intro p hp q hq hpq
        have hY : ∀ y ∈ ({(0, r₁), (0, r₂)} : Finset (Fin 2 × Fin 6)), y.2 ∉ X.image Prod.snd := by
          intro y hy
          rcases Finset.mem_insert.1 hy with rfl | hy
          · exact h1D
          · rw [Finset.mem_singleton] at hy; subst hy; exact h2D
        rcases Finset.mem_union.1 hp with hp | hp <;> rcases Finset.mem_union.1 hq with hq | hq
        · exact hX p hp q hq hpq
        · exact absurd (hpq ▸ Finset.mem_image_of_mem Prod.snd hp) (hY q hq)
        · exact absurd (hpq.symm ▸ Finset.mem_image_of_mem Prod.snd hq) (hY p hp)
        · simp only [Finset.mem_insert, Finset.mem_singleton] at hp hq
          rcases hp with rfl | rfl <;> rcases hq with rfl | rfl <;> rfl
    obtain ⟨i, hi, hsat⟩ := h {0, 1} 2 1 hcoh
    revert i
    decide
