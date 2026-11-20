import AFTD.Prelude
import AFTD.Kb.Tcs.Op309GraphFourDegenerate

/-!
# op309_four_degenerate_graph_five_colorable

Topic: graphs   Node: 3047c043aa77

Provenance: helper lemma. Standard finite greedy coloring, for the OP-309 path-port route.

Every finite four-degenerate graph is five-colorable by greedy coloring.
-/

theorem op309_four_degenerate_graph_five_colorable
    {W : Type*} [Fintype W] [DecidableEq W] (Q : SimpleGraph W)
    (hQ : op309_graph_four_degenerate Q) :
    Nonempty (Q.Coloring (Fin 5)) := by
  classical
  have hpart : ∀ S : Finset W, ∃ c : W → Fin 5,
      ∀ u ∈ S, ∀ v ∈ S, Q.Adj u v → c u ≠ c v := by
    intro S
    induction S using Finset.strongInductionOn with
    | _ S ih =>
      by_cases hs : S.Nonempty
      · obtain ⟨v, hv, T, hT, hcover⟩ := hQ S hs
        obtain ⟨c, hc⟩ := ih (S.erase v) (Finset.erase_ssubset hv)
        have hcard : (T.image c).card < (Finset.univ : Finset (Fin 5)).card := by
          have hi := Finset.card_image_le (s := T) (f := c)
          simp only [Finset.card_univ, Fintype.card_fin]
          omega
        obtain ⟨color, _, hcolor⟩ := Finset.exists_mem_notMem_of_card_lt_card hcard
        refine ⟨Function.update c v color, ?_⟩
        intro a ha b hb hab
        by_cases h1 : a = v
        · subst a
          have hne : b ≠ v := by
            intro h
            subst b
            exact Q.loopless.irrefl v hab
          have hbT := hcover b hb hab
          have hnot : c b ≠ color := by
            intro h
            apply hcolor
            exact Finset.mem_image.mpr ⟨b, hbT, h⟩
          simpa [Function.update, hne, Ne.symm hne] using hnot.symm
        · by_cases h2 : b = v
          · subst b
            have haT := hcover a ha hab.symm
            have hnot : c a ≠ color := by
              intro h
              apply hcolor
              exact Finset.mem_image.mpr ⟨a, haT, h⟩
            simpa [Function.update, h1, Ne.symm h1] using hnot
          · have ha' : a ∈ S.erase v := Finset.mem_erase.mpr ⟨h1,ha⟩
            have hb' : b ∈ S.erase v := Finset.mem_erase.mpr ⟨h2,hb⟩
            simpa [Function.update, h1, h2, Ne.symm h1, Ne.symm h2] using hc a ha' b hb' hab
      · refine ⟨fun _ => 0, ?_⟩
        intro a ha
        exact (hs ⟨a,ha⟩).elim
  obtain ⟨c,hc⟩ := hpart Finset.univ
  exact ⟨SimpleGraph.Coloring.mk c (fun hab => hc _ (Finset.mem_univ _) _ (Finset.mem_univ _) hab)⟩
