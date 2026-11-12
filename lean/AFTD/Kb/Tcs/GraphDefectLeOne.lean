import AFTD.Prelude
import AFTD.Kb.Tcs.Weight

/-!
# graph_defect_le_one

Topic: combinatorics   Node: fb09efdfcf2d

Provenance: formalization of a published result. Source: arXiv:2611.14160 Lemma 3.7

For every graph G on at least one vertex and every integer t ≥ 2, the defect def_t(G) satisfies def_t(G) ≤ 1. That is, the least nonnegative integer d such that every Z_t-labeling of K_{2n} either provides a vertex-disjoint copy of the same weight for each copy of G, or contains two copies of G with different weights on some subset of at most n + d vertices, is at most 1.
-/

open Classical in
/-- For a labelling of the complete graph on `2 * |α|` vertices: either every copy of `G` has a
vertex-disjoint copy of the same weight, or two copies of `G` with different weights both live on a
set of at most `|α| + 1` vertices. -/
private lemma graph_defect_le_one_aux {α : Type*} [Fintype α] [Nonempty α] (G : SimpleGraph α) (t : ℕ)
    {V : Type*} [Fintype V] [DecidableEq V]
    (hV : Fintype.card V = 2 * Fintype.card α)
    (C : SimpleGraph.TopEdgeLabeling V (ZMod t)) :
    let cw : SimpleGraph.Copy G (⊤ : SimpleGraph V) → ZMod t := fun f => ∑ e : G.edgeSet, C (f.mapEdgeSet e)
    (∀ (f₁ : SimpleGraph.Copy G (⊤ : SimpleGraph V)), ∃ (f₂ : SimpleGraph.Copy G (⊤ : SimpleGraph V)),
        Disjoint (Set.range f₁) (Set.range f₂) ∧ cw f₁ = cw f₂) ∨
    (∃ (U : Finset V), U.card ≤ Fintype.card α + 1 ∧
      ∃ (f₁ f₂ : SimpleGraph.Copy G (⊤ : SimpleGraph V)),
        (∀ v, f₁ v ∈ U) ∧ (∀ v, f₂ v ∈ U) ∧ cw f₁ ≠ cw f₂) := by
  intro cw
  by_cases hA : ∃ (U : Finset V), U.card ≤ Fintype.card α + 1 ∧
      ∃ (f₁ f₂ : SimpleGraph.Copy G (⊤ : SimpleGraph V)),
        (∀ v, f₁ v ∈ U) ∧ (∀ v, f₂ v ∈ U) ∧ cw f₁ ≠ cw f₂
  · exact Or.inr hA
  · left
    have key : ∀ (U : Finset V), U.card ≤ Fintype.card α + 1 →
        ∀ (f g : SimpleGraph.Copy G (⊤ : SimpleGraph V)),
        (∀ v, f v ∈ U) → (∀ v, g v ∈ U) → cw f = cw g := by
      intro U hU f g hf hg
      by_contra hne
      exact hA ⟨U, hU, f, g, hf, hg, hne⟩
    have hex : ∀ (T : Finset V), T.card = Fintype.card α →
        ∃ f : SimpleGraph.Copy G (⊤ : SimpleGraph V), ∀ v, f v ∈ T := by
      intro T hT
      have hc : Fintype.card α = Fintype.card T := by rw [Fintype.card_coe, hT]
      let e : α ≃ T := Fintype.equivOfCardEq hc
      let g : α → V := fun a => (e a : V)
      have hg : Function.Injective g := fun a b h => e.injective (Subtype.coe_injective h)
      refine ⟨SimpleGraph.Copy.mk ⟨g, ?_⟩ hg, fun a => (e a).2⟩
      intro a b hab
      simp only [SimpleGraph.top_adj]
      exact fun h => G.ne_of_adj hab (hg h)
    let w : Finset V → ZMod t := fun T => if h : ∃ f : SimpleGraph.Copy G (⊤ : SimpleGraph V), ∀ v, f v ∈ T
        then cw (Classical.choose h) else 0
    have w_eq : ∀ (T : Finset V), T.card ≤ Fintype.card α + 1 →
        ∀ (f : SimpleGraph.Copy G (⊤ : SimpleGraph V)), (∀ v, f v ∈ T) → w T = cw f := by
      intro T hT f hf
      have hhex : ∃ g : SimpleGraph.Copy G (⊤ : SimpleGraph V), ∀ v, g v ∈ T := ⟨f, hf⟩
      show (if h : ∃ f : SimpleGraph.Copy G (⊤ : SimpleGraph V), ∀ v, f v ∈ T
          then cw (Classical.choose h) else 0) = cw f
      rw [dif_pos hhex]
      exact key T hT _ _ (Classical.choose_spec hhex) hf
    have hswap : ∀ (A B : Finset V), A.card = Fintype.card α → B.card = Fintype.card α →
        (A ∪ B).card ≤ Fintype.card α + 1 → w A = w B := by
      intro A B hA hB hAB
      obtain ⟨f, hf⟩ := hex A hA
      obtain ⟨g, hg⟩ := hex B hB
      rw [w_eq A (by omega) f hf, w_eq B (by omega) g hg]
      exact key (A ∪ B) hAB f g (fun v => Finset.mem_union_left _ (hf v))
        (fun v => Finset.mem_union_right _ (hg v))
    have hconst : ∀ (A B : Finset V), A.card = Fintype.card α → B.card = Fintype.card α →
        w A = w B := by
      intro A B hA hB
      suffices H : ∀ k, ∀ (A B : Finset V), A.card = Fintype.card α → B.card = Fintype.card α →
          (A \ B).card ≤ k → w A = w B from H _ A B hA hB le_rfl
      intro k
      induction k with
      | zero =>
        intro A B hA hB hk
        have hsub : A ⊆ B :=
          Finset.sdiff_eq_empty_iff_subset.mp (Finset.card_eq_zero.mp (Nat.le_zero.mp hk))
        have hEq : A = B := Finset.eq_of_subset_of_card_le hsub (by omega)
        rw [hEq]
      | succ k ih =>
        intro A B hA hB hk
        by_cases hsub : A ⊆ B
        · have hEq : A = B := Finset.eq_of_subset_of_card_le hsub (by omega)
          rw [hEq]
        · obtain ⟨a, ha⟩ := Finset.sdiff_nonempty.mpr hsub
          have haA : a ∈ A := (Finset.mem_sdiff.mp ha).1
          have haB : a ∉ B := (Finset.mem_sdiff.mp ha).2
          have hcardEq : (B \ A).card = (A \ B).card := by
            rw [Finset.card_sdiff, Finset.card_sdiff, Finset.inter_comm, hA, hB]
          have hpos : 0 < (A \ B).card := Finset.card_pos.mpr ⟨a, ha⟩
          obtain ⟨b, hb⟩ := Finset.card_pos.mp (by omega : 0 < (B \ A).card)
          have hbB : b ∈ B := (Finset.mem_sdiff.mp hb).1
          have hbA : b ∉ A := (Finset.mem_sdiff.mp hb).2
          set A₁ : Finset V := insert b (A.erase a) with hA₁def
          have hbnot : b ∉ A.erase a := fun h => hbA (Finset.mem_of_mem_erase h)
          have hA₁card : A₁.card = Fintype.card α := by
            have h1 := Finset.card_insert_of_notMem hbnot
            have h2 := Finset.card_erase_add_one haA
            rw [hA₁def]
            omega
          have hdiff : A₁ \ B = (A \ B).erase a := by
            rw [hA₁def]
            ext x
            simp only [Finset.mem_sdiff, Finset.mem_insert, Finset.mem_erase]
            constructor
            · rintro ⟨hx, hxB⟩
              rcases hx with hxb | ⟨hxa, hxA⟩
              · subst hxb; exact absurd hbB hxB
              · exact ⟨hxa, ⟨hxA, hxB⟩⟩
            · intro h
              exact ⟨Or.inr ⟨h.1, h.2.1⟩, h.2.2⟩
          have hdiffcard : (A₁ \ B).card ≤ k := by
            rw [hdiff, Finset.card_erase_of_mem ha]
            omega
          have hunion : (A ∪ A₁).card ≤ Fintype.card α + 1 := by
            have hun : A ∪ A₁ = insert b A := by
              rw [hA₁def]
              ext x
              simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_erase]
              constructor
              · rintro (h | rfl | ⟨hxa, hxA⟩)
                · exact Or.inr h
                · exact Or.inl rfl
                · exact Or.inr hxA
              · rintro (rfl | h)
                · exact Or.inr (Or.inl rfl)
                · exact Or.inl h
            rw [hun, Finset.card_insert_of_notMem hbA, hA]
          exact (hswap A A₁ hA hA₁card hunion).trans (ih A₁ B hA₁card hB hdiffcard)
    intro f₁
    let S : Finset V := Finset.univ.image f₁
    have hS : S.card = Fintype.card α := by
      have hinj : Function.Injective (⇑f₁) := f₁.injective
      rw [show S = Finset.univ.image f₁ from rfl, Finset.card_image_of_injective _ hinj]
      simp
    let T : Finset V := Sᶜ
    have hT : T.card = Fintype.card α := by
      rw [show T = Sᶜ from rfl, Finset.card_compl, hS, hV]
      omega
    obtain ⟨f₂, hf₂⟩ := hex T hT
    refine ⟨f₂, ?_, ?_⟩
    · rw [Set.disjoint_left]
      intro x hx1 hx2
      have hxS : x ∈ S := by
        obtain ⟨v, hv⟩ := hx1
        exact hv ▸ Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩
      obtain ⟨v, hv⟩ := hx2
      have hxT : f₂ v ∈ T := hf₂ v
      rw [hv] at hxT
      have hxS' : x ∉ S := by
        simpa only [T, Finset.mem_compl] using hxT
      exact hxS' hxS
    · have h1 : w S = cw f₁ :=
        w_eq S (by omega) f₁ (fun v => Finset.mem_image.mpr ⟨v, Finset.mem_univ v, rfl⟩)
      have h2 : w T = cw f₂ := w_eq T (by omega) f₂ hf₂
      have h3 : w S = w T := hconst S T hS hT
      rw [← h1, ← h2]
      exact h3

/-- Universal defect bound (Lemma 3.7): for every graph G on n >= 1 vertices and every t >= 2, the defect def_t(G) is at most 1. -/
theorem graph_defect_le_one {α : Type*} [Fintype α] [Nonempty α] (G : SimpleGraph α)
    (t : ℕ) (ht : 2 ≤ t) :
    let copyWeight (C : SimpleGraph.TopEdgeLabeling (Fin (2 * Fintype.card α)) (ZMod t))
        (f : SimpleGraph.Copy G (⊤ : SimpleGraph (Fin (2 * Fintype.card α)))) : ZMod t :=
      open Classical in ∑ e : G.edgeSet, C (f.mapEdgeSet e)
    sInf {d : ℕ |
      ∀ (C : SimpleGraph.TopEdgeLabeling (Fin (2 * Fintype.card α)) (ZMod t)),
        (∀ (f₁ : SimpleGraph.Copy G (⊤ : SimpleGraph (Fin (2 * Fintype.card α)))),
          ∃ (f₂ : SimpleGraph.Copy G (⊤ : SimpleGraph (Fin (2 * Fintype.card α)))),
            Disjoint (Set.range f₁) (Set.range f₂) ∧
            copyWeight C f₁ = copyWeight C f₂) ∨
        (∃ (U : Finset (Fin (2 * Fintype.card α))), U.card ≤ Fintype.card α + d ∧
          ∃ (f₁ f₂ : SimpleGraph.Copy G (⊤ : SimpleGraph (Fin (2 * Fintype.card α)))),
            (∀ v, f₁ v ∈ U) ∧ (∀ v, f₂ v ∈ U) ∧
            copyWeight C f₁ ≠ copyWeight C f₂)} ≤ 1 := by
  have _ : 2 ≤ t := ht
  dsimp only
  apply Nat.sInf_le
  intro C
  exact graph_defect_le_one_aux G t (by simp) C
