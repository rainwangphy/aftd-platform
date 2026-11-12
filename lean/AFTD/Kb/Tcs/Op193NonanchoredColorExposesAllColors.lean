import AFTD.Prelude

/-!
# op_193_nonanchored_color_exposes_all_colors

Topic: graphs   Node: 5708e578bb4b

Provenance: helper lemma. Formal abstraction of the recoloring argument in arXiv:2610.17884 Theorem 3.2.

In an optimal coloring of the stable k-sets of a cycle, any nonanchored color class gives a stable (k-1)-set whose disjoint stable k-sets realize every color.
-/

set_option maxHeartbeats 2000000

theorem in777_color_has_all_neighbors {V : Type*} (adj : V → V → Prop)
    (hsymm : Symmetric adj) (q : ℕ) (c : V → Fin (q+1))
    (hproper : ∀ U W, adj U W → c U ≠ c W)
    (hmin : ¬ ∃ d : V → Fin q, ∀ U W, adj U W → d U ≠ d W)
    (j : Fin (q+1)) :
    ∃ U, c U = j ∧ ∀ i, i ≠ j → ∃ W, adj U W ∧ c W = i := by
  classical
  by_contra hn
  have hm : ∀ U, c U = j → ∃ i, i ≠ j ∧ ∀ W, adj U W → c W ≠ i := by
    intro U hu
    by_contra hh
    push_neg at hh
    apply hn
    refine ⟨U, hu, ?_⟩
    intro i hi
    exact hh i hi
  let f : V → { i : Fin (q+1) // i ≠ j } := fun U =>
    if hu : c U = j then ⟨Classical.choose (hm U hu), (Classical.choose_spec (hm U hu)).1⟩
    else ⟨c U, hu⟩
  let e := (finSuccAboveEquiv j).symm
  apply hmin
  refine ⟨fun U => e (f U), ?_⟩
  intro U W hadj heq
  have hf : (f U).1 = (f W).1 := congrArg Subtype.val (e.injective heq)
  by_cases hu : c U = j
  · by_cases hw : c W = j
    · exact hproper U W hadj (hu.trans hw.symm)
    · have hmiss := (Classical.choose_spec (hm U hu)).2 W hadj
      simp [f, hu, hw] at hf
      exact hmiss hf.symm
  · by_cases hw : c W = j
    · have hmiss := (Classical.choose_spec (hm W hw)).2 U (hsymm hadj)
      simp [f, hu, hw] at hf
      exact hmiss hf
    · simp [f, hu, hw] at hf
      exact hproper U W hadj hf

theorem op_193_nonanchored_color_exposes_all_colors
    (m k q : ℕ) (hk : 2 ≤ k)
    (c : {S : Finset (Fin m) // S.card = k ∧
      (SimpleGraph.cycleGraph m).IsIndepSet (↑S : Set (Fin m))} → Fin (q+1))
    (hproper : ∀ U W, Disjoint U.1 W.1 → c U ≠ c W)
    (hmin : ¬ ∃ d : {S : Finset (Fin m) // S.card = k ∧
      (SimpleGraph.cycleGraph m).IsIndepSet (↑S : Set (Fin m))} → Fin q,
      ∀ U W, Disjoint U.1 W.1 → d U ≠ d W)
    (j : Fin (q+1))
    (hnoanchor : ∀ U, c U = j → ∃ W, c W = j ∧ (U.1 ∩ W.1).card < 2) :
    ∃ F : Finset (Fin m), F.card = k-1 ∧
      (SimpleGraph.cycleGraph m).IsIndepSet (↑F : Set (Fin m)) ∧
      ∀ i : Fin (q+1), ∃ U, c U = i ∧ Disjoint F U.1 := by
  classical
  let adj := fun U W : {S : Finset (Fin m) // S.card = k ∧
      (SimpleGraph.cycleGraph m).IsIndepSet (↑S : Set (Fin m))} => Disjoint U.1 W.1
  have hs : Symmetric adj := fun U W h => h.symm
  obtain ⟨U, hU, hneighbors⟩ := in777_color_has_all_neighbors adj hs q c hproper hmin j
  obtain ⟨W, hW, hsmall⟩ := hnoanchor U hU
  have hnot : ¬ Disjoint U.1 W.1 := by
    intro hd
    exact hproper U W hd (hU.trans hW.symm)
  have hpos : 0 < (U.1 ∩ W.1).card := Finset.card_pos.mpr (Finset.not_disjoint_iff_nonempty_inter.mp hnot)
  have hcard : (U.1 ∩ W.1).card = 1 := by omega
  let F := U.1 \ W.1
  have hf : F.card = k-1 := by
    have hh := Finset.card_sdiff_add_card_inter U.1 W.1
    rw [hcard, U.2.1] at hh
    dsimp [F]
    omega
  have hi : (SimpleGraph.cycleGraph m).IsIndepSet (↑F : Set (Fin m)) := by
    apply U.2.2.mono
    intro x hx
    exact (Finset.mem_sdiff.mp hx).1
  refine ⟨F, hf, hi, ?_⟩
  intro i
  by_cases hij : i = j
  · subst i
    exact ⟨W, hW, Finset.sdiff_disjoint⟩
  · obtain ⟨T, hd, hc⟩ := hneighbors i hij
    exact ⟨T, hc, hd.mono_left Finset.sdiff_subset⟩
