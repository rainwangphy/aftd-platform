import AFTD.Prelude
import AFTD.Kb.Tcs.Op869ColorSetAmplification

/-!
# op869_bipartite_gadget_growth

Topic: online_algorithms   Node: d390f8ea1216

Provenance: helper lemma. arXiv:2610.41516, Lemma 2.3

When two disjoint bipartite graphs are joined by a new vertex adjacent to a designated side of one, the combined graph has a bipartition with at least ceil(t/2) more colors on one side.
-/

def op869_gadget_side {α β : Type} (p : α → Bool) (q : β → Bool) (flip : Bool) : Option (α ⊕ β) → Bool
  | none => false
  | some (Sum.inl a) => p a
  | some (Sum.inr b) => if flip then !q b else q b

theorem op869_gadget_side_proper {α β : Type} (G : SimpleGraph (Option (α ⊕ β)))
    (p : α → Bool) (q : β → Bool)
    (hleft : ∀ a b, G.Adj (some (Sum.inl a)) (some (Sum.inl b)) → p a ≠ p b)
    (hright : ∀ a b, G.Adj (some (Sum.inr a)) (some (Sum.inr b)) → q a ≠ q b)
    (hcross : ∀ a b, ¬ G.Adj (some (Sum.inl a)) (some (Sum.inr b)))
    (hnewright : ∀ b, ¬ G.Adj none (some (Sum.inr b)))
    (hnewleft : ∀ a, G.Adj none (some (Sum.inl a)) → p a = true)
    (flip : Bool) : ∀ x y, G.Adj x y → op869_gadget_side p q flip x ≠ op869_gadget_side p q flip y := by
  intro x y h
  cases x with
  | none =>
    cases y with
    | none => exact False.elim (G.irrefl h)
    | some y =>
      cases y with
      | inl a => simpa [op869_gadget_side, hnewleft a h]
      | inr b => exact False.elim (hnewright b h)
  | some x =>
    cases x with
    | inl a =>
      cases y with
      | none => simpa [op869_gadget_side, hnewleft a h.symm]
      | some y =>
        cases y with
        | inl b => exact hleft a b h
        | inr b => exact False.elim (hcross a b h)
    | inr a =>
      cases y with
      | none => exact False.elim (hnewright a h.symm)
      | some y =>
        cases y with
        | inl b => exact False.elim (hcross b a h.symm)
        | inr b =>
          have hab := hright a b h
          cases flip <;> cases ha : q a <;> cases hb : q b <;>
            simp_all [op869_gadget_side]

/-- The graph-gluing growth step in the bipartite online-coloring gadget. -/
theorem op869_bipartite_gadget_growth {α β γ : Type} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ]
    (G : SimpleGraph (Option (α ⊕ β))) (colors : Option (α ⊕ β) → Finset γ)
    (p : α → Bool) (q : β → Bool) (a t : ℕ)
    (hleft : ∀ x y, G.Adj (some (Sum.inl x)) (some (Sum.inl y)) → p x ≠ p y)
    (hright : ∀ x y, G.Adj (some (Sum.inr x)) (some (Sum.inr y)) → q x ≠ q y)
    (hcross : ∀ x y, ¬ G.Adj (some (Sum.inl x)) (some (Sum.inr y)))
    (hnewright : ∀ y, ¬ G.Adj none (some (Sum.inr y)))
    (hnewleft : ∀ x, G.Adj none (some (Sum.inl x)) ↔ p x = true)
    (hproper : ∀ x y, G.Adj x y → Disjoint (colors x) (colors y))
    (hcard : (colors none).card = t)
    (hP : a ≤ ((Finset.univ.filter (fun x => p x = true)).biUnion
      (fun x => colors (some (Sum.inl x)))).card)
    (hQ : a ≤ ((Finset.univ.filter (fun x => q x = true)).biUnion
      (fun x => colors (some (Sum.inr x)))).card) :
    ∃ flip target : Bool,
      (∀ x y, G.Adj x y → op869_gadget_side p q flip x ≠ op869_gadget_side p q flip y) ∧
      a + (t+1)/2 ≤ ((Finset.univ.filter (fun x => op869_gadget_side p q flip x = target)).biUnion colors).card := by
  classical
  let P := (Finset.univ.filter (fun x => p x = true)).biUnion (fun x => colors (some (Sum.inl x)))
  let Q := (Finset.univ.filter (fun x => q x = true)).biUnion (fun x => colors (some (Sum.inr x)))
  have hdis : Disjoint (colors none) P := by
    apply Finset.disjoint_left.mpr
    intro c hc hcp
    obtain ⟨x, hx, hxc⟩ := Finset.mem_biUnion.mp hcp
    have hpx : p x = true := (Finset.mem_filter.mp hx).2
    exact Finset.disjoint_left.mp (hproper none _ ((hnewleft x).mpr hpx)) hc hxc
  have hgrow := op869_color_set_amplification P Q (colors none) a t hP hQ hcard hdis
  have hside (f : Bool) := op869_gadget_side_proper G p q hleft hright hcross hnewright
    (fun x hx => (hnewleft x).mp hx) f
  rcases hgrow with hPQ | hQX
  · refine ⟨false, true, hside false, le_trans hPQ (Finset.card_le_card ?_)⟩
    intro c hc
    rcases Finset.mem_union.mp hc with hc | hc
    · obtain ⟨x, hx, hxc⟩ := Finset.mem_biUnion.mp hc
      have hpx : p x = true := (Finset.mem_filter.mp hx).2
      exact Finset.mem_biUnion.mpr ⟨some (Sum.inl x), by simp [op869_gadget_side, hpx], hxc⟩
    · obtain ⟨x, hx, hxc⟩ := Finset.mem_biUnion.mp hc
      have hqx : q x = true := (Finset.mem_filter.mp hx).2
      exact Finset.mem_biUnion.mpr ⟨some (Sum.inr x), by simp [op869_gadget_side, hqx], hxc⟩
  · refine ⟨true, false, hside true, le_trans hQX (Finset.card_le_card ?_)⟩
    intro c hc
    rcases Finset.mem_union.mp hc with hc | hc
    · obtain ⟨x, hx, hxc⟩ := Finset.mem_biUnion.mp hc
      have hqx : q x = true := (Finset.mem_filter.mp hx).2
      exact Finset.mem_biUnion.mpr ⟨some (Sum.inr x), by simp [op869_gadget_side, hqx], hxc⟩
    · exact Finset.mem_biUnion.mpr ⟨none, by simp [op869_gadget_side], hc⟩
