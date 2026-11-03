import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# with_top_nat_lex_add_binary_le_iff

Topic: social_choice   Node: c9cb7d943bdd

Provenance: helper lemma. step towards swf_anonymous_stationary_monotone_upper_lower_dominance_exists

Pointwise addition of a binary shift sequence e : ℕ → {0, 1} strictly preserves and reflects the lexicographic order on WithTop ℕ streams.
-/

/-- Coordinate-wise addition of a {0, 1}-valued binary sequence preserves and reflects lexicographic order on sequences in WithTop ℕ (Claim 1 of Dubey et al. 2026). -/
theorem with_top_nat_lex_add_binary_le_iff
    (u v : Lex (ℕ → WithTop ℕ)) (e : ℕ → WithTop ℕ) (he : ∀ t, e t ≤ 1) :
    u ≤ v ↔ (toLex (ofLex u + e)) ≤ (toLex (ofLex v + e)) := by
  have he_ne_top : ∀ t, e t ≠ ⊤ := by
    intro t
    exact ne_top_of_lt (lt_of_le_of_lt (he t) (WithTop.coe_lt_top 1))
  have h_eq_fun : (ofLex u + e = ofLex v + e) ↔ (ofLex u = ofLex v) := by
    constructor
    · intro h
      ext t
      exact (WithTop.add_right_inj (he_ne_top t)).1 (by simpa using congrFun h t)
    · intro h
      rw [h]
  have h_lt : u < v ↔ toLex (ofLex u + e) < toLex (ofLex v + e) := by
    change Pi.Lex (· < ·) (· < ·) (ofLex u) (ofLex v) ↔
      Pi.Lex (· < ·) (· < ·) (ofLex u + e) (ofLex v + e)
    constructor
    · rintro ⟨i, hi, hlt⟩
      refine ⟨i, ?_, ?_⟩
      · intro j hj
        simpa using congrArg (fun x => x + e j) (hi j hj)
      · simpa only [Pi.add_apply] using
          (WithTop.add_lt_add_iff_right (he_ne_top i)).2 hlt
    · rintro ⟨i, hi, hlt⟩
      refine ⟨i, ?_, ?_⟩
      · intro j hj
        exact (WithTop.add_right_inj (he_ne_top j)).1 (by simpa using hi j hj)
      · exact (WithTop.add_lt_add_iff_right (he_ne_top i)).1 (by simpa using hlt)
  have h_eq : (toLex (ofLex u + e) = toLex (ofLex v + e)) ↔ u = v := by
    rw [toLex_inj, h_eq_fun, ofLex_inj]
  rw [le_iff_lt_or_eq, le_iff_lt_or_eq]
  constructor
  · rintro (hlt | heq)
    · exact Or.inl (h_lt.mp hlt)
    · exact Or.inr (h_eq.mpr heq)
  · rintro (hlt | heq)
    · exact Or.inl (h_lt.mpr hlt)
    · exact Or.inr (h_eq.mp heq)
