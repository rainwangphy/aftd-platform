import AFTD.Prelude
import AFTD.Kb.Tcs.Op869OrientPairsHalf

/-!
# op869_two_sided_colors_by_orientation

Topic: online_algorithms   Node: 611e9111146e

Provenance: helper lemma. arXiv:2610.41516, Lemma 2.4, turning repeated colors into two-sided colors.

If each marked color occurs in at least two distinct copies, the copies can be oriented so at least half the marked colors occur on both sides.
-/

theorem op869_two_sided_colors_by_orientation {γ : Type} [DecidableEq γ] (m : ℕ) (C : Finset γ)
    (R : Fin m → γ → Prop) [DecidableRel R] :
    (∀ c ∈ C, ∃ a b : Fin m, a ≠ b ∧ R a c ∧ R b c) →
    ∃ s : Finset (Fin m), C.card ≤ 2 * (C.filter (fun c =>
      (∃ a : Fin m, a ∈ s ∧ R a c) ∧ (∃ b : Fin m, b ∉ s ∧ R b c))).card := by
  classical
  intro h
  cases m with
  | zero =>
      have hC : C = ∅ := by
        apply Finset.not_nonempty_iff_eq_empty.mp
        intro hn
        obtain ⟨c, hc⟩ := hn
        obtain ⟨a, b, hab, ha, hb⟩ := h c hc
        exact Fin.elim0 a
      simp [hC]
  | succ m =>
      let p : γ → Fin (m+1) × Fin (m+1) := fun c =>
        if hc : c ∈ C then (Classical.choose (h c hc), Classical.choose (Classical.choose_spec (h c hc))) else (0, 0)
      have hp : ∀ c ∈ C, (p c).1 ≠ (p c).2 ∧ R (p c).1 c ∧ R (p c).2 c := by
        intro c hc
        dsimp only [p]
        simp only [dif_pos hc]
        exact Classical.choose_spec (Classical.choose_spec (h c hc))
      obtain ⟨s, hs⟩ := op869_orient_pairs_half (m+1) C (fun c => (p c).1) (fun c => (p c).2)
        (fun c hc => (hp c hc).1)
      refine ⟨s, le_trans hs (Nat.mul_le_mul_left 2 ?_)⟩
      apply Finset.card_le_card
      intro c hc
      simp only [Finset.mem_filter] at hc ⊢
      refine ⟨hc.1, ?_⟩
      rcases hc.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨⟨(p c).1, h1, (hp c hc.1).2.1⟩, ⟨(p c).2, h2, (hp c hc.1).2.2⟩⟩
      · exact ⟨⟨(p c).2, h2, (hp c hc.1).2.2⟩, ⟨(p c).1, h1, (hp c hc.1).2.1⟩⟩
