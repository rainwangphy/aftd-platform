import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ApxParadox
import AFTD.Kb.GameTheoryEconomics.ApxSearch

/-!
# apx_search_sound

Topic: social_choice   Node: 3d59742b01a7

If the pruned search succeeds, every seat assignment choosing candidates for the profiles has a population paradox between two of them.
-/

/-- Soundness of `apx_search`: if it succeeds, every seat assignment `g` that agrees with the done part and picks candidates for the pending profiles has a population paradox between two of the profiles. -/
lemma apx_search_sound (g : (Fin 4 → ℕ) → (Fin 4 → ℕ)) (Pos : (Fin 4 → ℕ) → Prop) :
    ∀ todo done, apx_search done todo = true → (∀ x ∈ done, g x.1 = x.2 ∧ Pos x.1) →
      (∀ pc ∈ todo, g pc.1 ∈ pc.2 ∧ Pos pc.1) →
      ∃ p q, Pos p ∧ Pos q ∧ apx_paradox p (g p) q (g q) = true := by
  intro todo
  induction todo with
  | nil => intro done h; simp [apx_search] at h
  | cons pc rest ih =>
    intro done h hdone htodo
    obtain ⟨p, cs⟩ := pc
    simp only [apx_search, List.all_eq_true] at h
    obtain ⟨hmem, hpos⟩ := htodo (p, cs) (by simp)
    have := h (g p) hmem
    rcases Bool.or_eq_true_iff.1 this with hc | hs
    · obtain ⟨x, hx, hxp⟩ := List.any_eq_true.1 hc
      obtain ⟨hgx, hposx⟩ := hdone x hx
      rcases Bool.or_eq_true_iff.1 hxp with h1 | h1
      · exact ⟨x.1, p, hposx, hpos, by rw [hgx]; exact h1⟩
      · exact ⟨p, x.1, hpos, hposx, by rw [hgx]; exact h1⟩
    · refine ih ((p, g p) :: done) hs ?_ (fun pc hpc => htodo pc (by simp [hpc]))
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact ⟨rfl, hpos⟩
      · exact hdone x hx
