import AFTD.Prelude
import AFTD.Kb.Tcs.IsStronglyChromaticChoosable

/-!
# cycle_five_compl_strongly_chromatic_choosable

Topic: graphs   Node: df21c91cd8e3

Provenance: formalization of a published result. Source: arXiv:2610.14241 (Restricting odd antiholes in critical graphs via list coloring), remark after Conjecture 9 (the case ℓ = 3 is the well-known fact that a cycle with 2-lists is colorable unless all lists are equal); partial result for OP-216

The case ℓ = 3 of Conjecture 9: the complement of C_5 (itself a 5-cycle) is strongly 3-chromatic-choosable: χ = 3 and it is colorable from any lists of size 2 that are not all equal.
-/

theorem cycle_five_compl_adj_iff (u v : Fin 5) :
    (SimpleGraph.cycleGraph 5)ᶜ.Adj u v ↔
      (![0, 3, 1, 4, 2] : Fin 5 → Fin 5) v = (![0, 3, 1, 4, 2] : Fin 5 → Fin 5) u + 1 ∨
      (![0, 3, 1, 4, 2] : Fin 5 → Fin 5) u = (![0, 3, 1, 4, 2] : Fin 5 → Fin 5) v + 1 := by
  revert u v; decide

theorem cycle_five_compl_not_two_colorable :
    ∀ f : Fin 5 → Fin 2, ∃ u v, (SimpleGraph.cycleGraph 5)ᶜ.Adj u v ∧ f u = f v := by
  decide

theorem finset_card_two_exists_ne (s : Finset ℕ) (hs : s.card = 2) (b : ℕ) : ∃ y ∈ s, y ≠ b := by
  obtain ⟨x, y, hxy, rfl⟩ := Finset.card_eq_two.mp hs
  by_cases hx : x = b
  · exact ⟨y, by simp, fun h => hxy (hx.trans h.symm)⟩
  · exact ⟨x, by simp, hx⟩

theorem cycle_five_compl_strongly_chromatic_choosable :
    IsStronglyChromaticChoosable (SimpleGraph.cycleGraph 5)ᶜ 3 := by
  classical
  set p : Fin 5 → Fin 5 := ![0, 2, 4, 1, 3] with hp
  set q : Fin 5 → Fin 5 := ![0, 3, 1, 4, 2] with hq
  have hpq : ∀ u, p (q u) = u := by decide
  refine ⟨?_, ?_⟩
  · have h3 : (SimpleGraph.cycleGraph 5)ᶜ.Colorable 3 :=
      ⟨SimpleGraph.Coloring.mk (fun u => (⟨u.val / 2, by omega⟩ : Fin 3)) (by
        intro u v huv
        revert huv
        revert u v
        decide)⟩
    have h2 : ¬ (SimpleGraph.cycleGraph 5)ᶜ.Colorable 2 := by
      rintro ⟨f⟩
      obtain ⟨u, v, huv, hf⟩ := cycle_five_compl_not_two_colorable f
      exact f.valid huv hf
    have := (SimpleGraph.chromaticNumber_eq_iff_colorable_not_colorable (n := 2)).mpr ⟨h3, h2⟩
    exact this.trans (by norm_num)
  · intro L hL hne
    have hL2 : ∀ v, (L v).card = 2 := hL
    -- a consecutive pair (in the cycle order p of the complement) with different lists
    have hcons : ∃ t : Fin 5, L (p t) ≠ L (p (t + 1)) := by
      by_contra h
      push Not at h
      have hall : ∀ s : Fin 5, L (p s) = L (p 0) := by
        intro s
        have e1 := h 0; have e2 := h 1; have e3 := h 2; have e4 := h 3
        fin_cases s
        · rfl
        · exact e1.symm
        · exact (e1.trans e2).symm
        · exact (e1.trans (e2.trans e3)).symm
        · exact (e1.trans (e2.trans (e3.trans e4))).symm
      obtain ⟨u, v, huv⟩ := hne
      apply huv
      rw [← hpq u, ← hpq v, hall (q u), hall (q v)]
    obtain ⟨t, ht⟩ := hcons
    obtain ⟨a, haA, haB⟩ : ∃ a ∈ L (p t), a ∉ L (p (t + 1)) := by
      by_contra h
      push Not at h
      exact ht (Finset.eq_of_subset_of_card_le h (by rw [hL2, hL2]))
    obtain ⟨c1, hc1, hc1a⟩ := finset_card_two_exists_ne (L (p (t - 1))) (hL2 _) a
    obtain ⟨c2, hc2, hc21⟩ := finset_card_two_exists_ne (L (p (t - 2))) (hL2 _) c1
    obtain ⟨c3, hc3, hc32⟩ := finset_card_two_exists_ne (L (p (t - 3))) (hL2 _) c2
    obtain ⟨c4, hc4, hc43⟩ := finset_card_two_exists_ne (L (p (t - 4))) (hL2 _) c3
    have ht4 : t - 4 = t + 1 := by
      have key : ∀ x : Fin 5, x - 4 = x + 1 := by decide
      exact key t
    have hc4a : c4 ≠ a := by
      intro h; rw [ht4] at hc4; exact haB (h ▸ hc4)
    set col : Fin 5 → ℕ := ![a, c1, c2, c3, c4] with hcol
    have hcolmem : ∀ k : Fin 5, col k ∈ L (p (t - k)) := by
      intro k
      fin_cases k
      · simpa [hcol] using haA
      · simpa [hcol] using hc1
      · simpa [hcol] using hc2
      · simpa [hcol] using hc3
      · simpa [hcol] using hc4
    have hcolne : ∀ k : Fin 5, col (k + 1) ≠ col k := by
      intro k
      fin_cases k
      · simpa [hcol] using hc1a
      · simpa [hcol] using hc21
      · simpa [hcol] using hc32
      · simpa [hcol] using hc43
      · simpa [hcol] using hc4a.symm
    refine ⟨fun u => col (t - q u), ?_, ?_⟩
    · intro u
      have := hcolmem (t - q u)
      rwa [sub_sub_cancel, hpq] at this
    · intro u v huv
      have hadj := (cycle_five_compl_adj_iff u v).mp huv
      rw [← hq] at hadj
      rcases hadj with h | h
      · have e : t - q v + 1 = t - q u := by rw [h]; abel
        have := hcolne (t - q v)
        rw [e] at this
        exact this
      · have e : t - q u + 1 = t - q v := by rw [h]; abel
        have := hcolne (t - q u)
        rw [e] at this
        exact fun h' => this h'.symm
