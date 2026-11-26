import AFTD.Prelude
import AFTD.Kb.Tcs.IsKExtendable

/-!
# pairwise_intersecting_edges_have_center

Topic: graphs   Node: 61b184915e55

Provenance: helper lemma. Balanced-cut k=7 reduction for OP-1957; https://arxiv.org/abs/2611.22690.

A finite graph with at least four vertices, no isolated vertex and pairwise intersecting edges has a common endpoint for all edges.
-/

theorem pairwise_intersecting_edges_have_center
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (F : Finset V)
    (hcard : 4 ≤ F.card)
    (hnoniso : ∀ u ∈ F, ∃ v ∈ F, G.Adj u v)
    (hnodis : ∀ a ∈ F, ∀ b ∈ F, ∀ c ∈ F, ∀ d ∈ F,
      G.Adj a b → G.Adj c d → a=c ∨ a=d ∨ b=c ∨ b=d) :
    ∃ z ∈ F, ∀ u ∈ F, ∀ v ∈ F, G.Adj u v → u=z ∨ v=z := by
  set_option maxHeartbeats 4000000 in
    classical
    have hnF : F.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨a,ha⟩ := hnF
    obtain ⟨b,hb,hab⟩ := hnoniso a ha
    have habne : a ≠ b := G.ne_of_adj hab
    by_cases haall : ∀ u ∈ F, ∀ v ∈ F, G.Adj u v → u=a ∨ v=a
    · exact ⟨a,ha,haall⟩
    · push Not at haall
      obtain ⟨c,hc,d,hd,hcd,hca,hda⟩ := haall
      have hmeet := hnodis a ha b hb c hc d hd hab hcd
      have hbc : ∃ c ∈ F, G.Adj b c ∧ c ≠ a := by
        rcases hmeet with hac | had | hbc | hbd
        · exact False.elim (hca hac.symm)
        · exact False.elim (hda had.symm)
        · refine ⟨d,hd,?_,hda⟩
          simpa [hbc] using hcd
        · refine ⟨c,hc,?_,hca⟩
          simpa [hbd] using hcd.symm
      obtain ⟨c,hc,hbc,hca⟩ := hbc
      have hcb : c ≠ b := (G.ne_of_adj hbc).symm
      have hnot : ¬ F ⊆ ({a,b,c} : Finset V) := by
        intro hh
        have h1 := Finset.card_le_card hh
        have h2 : ({a,b,c} : Finset V).card ≤ 3 := Finset.card_le_three
        omega
      obtain ⟨d,hd,hdnot⟩ := Finset.not_subset.mp hnot
      have hda : d ≠ a := by intro he; apply hdnot; simp [he]
      have hdb : d ≠ b := by intro he; apply hdnot; simp [he]
      have hdc : d ≠ c := by intro he; apply hdnot; simp [he]
      obtain ⟨e,he,hde⟩ := hnoniso d hd
      have heq : e=b := by
        have h1 := hnodis a ha b hb d hd e he hab hde
        have h2 := hnodis b hb c hc d hd e he hbc hde
        have h1' : a=e ∨ b=e := by
          rcases h1 with h | h | h | h
          · exact False.elim (hda h.symm)
          · exact Or.inl h
          · exact False.elim (hdb h.symm)
          · exact Or.inr h
        have h2' : b=e ∨ c=e := by
          rcases h2 with h | h | h | h
          · exact False.elim (hdb h.symm)
          · exact Or.inl h
          · exact False.elim (hdc h.symm)
          · exact Or.inr h
        rcases h1' with hae | hbe
        · rcases h2' with hbe | hce
          · exact hbe.symm
          · exact False.elim (hca (hce.trans hae.symm))
        · exact hbe.symm
      have hbd : G.Adj b d := by simpa [heq] using hde.symm
      refine ⟨b,hb,?_⟩
      intro u hu v hv huv
      by_contra hn
      push Not at hn
      have h1 := hnodis a ha b hb u hu v hv hab huv
      have h2 := hnodis b hb d hd u hu v hv hbd huv
      have h3 := hnodis b hb c hc u hu v hv hbc huv
      have h1' : a=u ∨ a=v := by
        rcases h1 with h | h | h | h
        · exact Or.inl h
        · exact Or.inr h
        · exact False.elim (hn.1 h.symm)
        · exact False.elim (hn.2 h.symm)
      have h2' : d=u ∨ d=v := by
        rcases h2 with h | h | h | h
        · exact False.elim (hn.1 h.symm)
        · exact False.elim (hn.2 h.symm)
        · exact Or.inl h
        · exact Or.inr h
      have h3' : c=u ∨ c=v := by
        rcases h3 with h | h | h | h
        · exact False.elim (hn.1 h.symm)
        · exact False.elim (hn.2 h.symm)
        · exact Or.inl h
        · exact Or.inr h
      rcases h1' with h1 | h1 <;> rcases h2' with h2 | h2 <;> rcases h3' with h3 | h3 <;> subst_vars <;> simp_all
