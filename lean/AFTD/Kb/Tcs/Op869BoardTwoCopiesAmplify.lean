import AFTD.Prelude
import AFTD.Kb.Tcs.Op869DisjointSpliceBipartition
import AFTD.Kb.Tcs.Op869SplicedColorsUpdate
import AFTD.Kb.Tcs.Op869ColorSetAmplification
import AFTD.Kb.Tcs.Op869BipartiteGadgetGrowth
import AFTD.Kb.Tcs.Op869GraphFromPredecessors
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# op869_board_two_copies_amplify

Topic: online_algorithms   Node: f1840f145009

Provenance: helper lemma. arXiv:2610.41516, Lemma 2.3

On the actual finite board, after two disjoint bipartite copies and a new vertex joined to the first designated side, one can orient the graph so that a side gains at least ceil(t/2) colors.
-/

theorem op869_add_root_to_bipartition {n : ℕ} (P : Fin n → Finset (Fin n))
    (i : Fin n) (S : Finset (Fin n)) (side : Fin n → Bool)
    (hclear : ∀ a, i.val ≤ a.val → P a = ∅)
    (hS : ∀ a ∈ S, a < i)
    (hside : ∀ a b, (op869_graph_from_predecessors P).Adj a b → side a ≠ side b)
    (hSside : ∀ a ∈ S, side a = true) :
    ∃ side' : Fin n → Bool,
      (∀ a, a ≠ i → side' a = side a) ∧ side' i = false ∧
      ∀ a b, (op869_graph_from_predecessors (Function.update P i S)).Adj a b → side' a ≠ side' b := by
  classical
  let P' := Function.update P i S
  let side' := Function.update side i false
  have hroot (a : Fin n) : (op869_graph_from_predecessors P').Adj a i → a ∈ S := by
    intro hadj
    change (a < i ∧ a ∈ P' i) ∨ (i < a ∧ i ∈ P' a) at hadj
    rcases hadj with ⟨_,ha⟩ | ⟨hia,ha⟩
    · simpa [P'] using ha
    · have hai : a ≠ i := ne_of_gt hia
      have hp : P' a = ∅ := by
        simp [P', Function.update_of_ne hai, hclear a (le_of_lt hia)]
      simp [hp] at ha
  have hpreserve (a b : Fin n) (ha : a ≠ i) (hb : b ≠ i) :
      (op869_graph_from_predecessors P').Adj a b → (op869_graph_from_predecessors P).Adj a b := by
    intro hadj
    change (a < b ∧ a ∈ P' b) ∨ (b < a ∧ b ∈ P' a) at hadj
    change (a < b ∧ a ∈ P b) ∨ (b < a ∧ b ∈ P a)
    simpa [P', Function.update_of_ne ha, Function.update_of_ne hb] using hadj
  refine ⟨side', ?_, ?_, ?_⟩
  · intro a ha
    simp [side', Function.update_of_ne ha]
  · simp [side']
  · intro a b hadj
    by_cases ha : a = i
    · subst a
      have hb : b ≠ i := by
        intro heq
        subst b
        exact (op869_graph_from_predecessors P').irrefl hadj
      have hs := hSside b (hroot b hadj.symm)
      simp [side', Function.update_of_ne hb, hs]
    · by_cases hb : b = i
      · subst b
        have hs := hSside a (hroot a hadj)
        simp [side', Function.update_of_ne ha, hs]
      · simpa [side', Function.update_of_ne ha, Function.update_of_ne hb] using
          hside a b (hpreserve a b ha hb hadj)

theorem op869_bool_bipartition_colorable {n : ℕ} (G : SimpleGraph (Fin n))
    (side : Fin n → Bool)
    (hside : ∀ a b, G.Adj a b → side a ≠ side b) : G.Colorable 2 := by
  refine ⟨SimpleGraph.Coloring.mk (fun a => if side a then (1 : Fin 2) else 0) ?_⟩
  intro a b hab
  have hd := hside a b hab
  cases ha : side a <;> cases hb : side b <;> simp_all


def op869_gadget_join_graph {α β : Type} (G₁ : SimpleGraph α) (G₂ : SimpleGraph β) (p : α → Bool) :
    SimpleGraph (Option (α ⊕ β)) where
  Adj x y := match x,y with
    | none, some (Sum.inl a) => p a = true
    | some (Sum.inl a), none => p a = true
    | some (Sum.inl a), some (Sum.inl b) => G₁.Adj a b
    | some (Sum.inr a), some (Sum.inr b) => G₂.Adj a b
    | _, _ => False
  symm := by
    constructor
    intro x y h
    cases x with
    | none => cases y with
      | none => exact h
      | some y => cases y <;> exact h
    | some x =>
      cases x with
      | inl a => cases y with
        | none => exact h
        | some y => cases y with
          | inl b => exact h.symm
          | inr b => exact h
      | inr a => cases y with
        | none => exact h
        | some y => cases y with
          | inl b => exact h
          | inr b => exact h.symm
  loopless := by
    constructor
    intro x
    cases x with
    | none => simp
    | some x => cases x with
      | inl a => exact G₁.irrefl
      | inr b => exact G₂.irrefl

def op869_gadget_join_colors {α β γ : Type} (c₁ : α → Finset γ) (c₂ : β → Finset γ) (X : Finset γ) :
    Option (α ⊕ β) → Finset γ
  | none => X
  | some (Sum.inl a) => c₁ a
  | some (Sum.inr b) => c₂ b

structure Op869GadgetCert {V γ : Type} [Fintype V] [DecidableEq V] [DecidableEq γ]
    (G : SimpleGraph V) (C : V → Finset γ) (t j : ℕ) where
  color_card : ∀ v, (C v).card = t
  proper : ∀ x y, G.Adj x y → Disjoint (C x) (C y)
  side : V → Bool
  bipartite : ∀ x y, G.Adj x y → side x ≠ side y
  large : t+j*((t+1)/2) ≤ ((Finset.univ.filter (fun v => side v = true)).biUnion C).card
  size : Fintype.card V ≤ 2^(j+1)-1

theorem op869_gadget_recursive_merge {α β γ : Type} [Fintype α] [Fintype β]
    [DecidableEq α] [DecidableEq β] [DecidableEq γ] (t j : ℕ)
    (G₁ : SimpleGraph α) (G₂ : SimpleGraph β) (C₁ : α → Finset γ) (C₂ : β → Finset γ)
    (L : Op869GadgetCert G₁ C₁ t j) (R : Op869GadgetCert G₂ C₂ t j) (X : Finset γ)
    (hX : X.card = t)
    (hdis : Disjoint X ((Finset.univ.filter (fun v : α => L.side v = true)).biUnion C₁)) :
    Nonempty (Op869GadgetCert (op869_gadget_join_graph G₁ G₂ L.side)
      (op869_gadget_join_colors C₁ C₂ X) t (j+1)) := by
  classical
  let G := op869_gadget_join_graph G₁ G₂ L.side
  let C := op869_gadget_join_colors C₁ C₂ X
  have hnewproper (x : α) (hx : L.side x = true) : Disjoint X (C₁ x) := by
    apply Finset.disjoint_left.mpr
    intro c hc hxc
    have hcP : c ∈ (Finset.univ.filter (fun v : α => L.side v = true)).biUnion C₁ :=
      Finset.mem_biUnion.mpr ⟨x, by simp [hx], hxc⟩
    exact Finset.disjoint_left.mp hdis hc hcP
  have hproper : ∀ x y, G.Adj x y → Disjoint (C x) (C y) := by
    intro x y h
    cases x with
    | none =>
      cases y with
      | none => exact False.elim (G.irrefl h)
      | some y =>
        cases y with
        | inl a => exact hnewproper a h
        | inr b => exact False.elim h
    | some x =>
      cases x with
      | inl a =>
        cases y with
        | none => exact (hnewproper a h).symm
        | some y =>
          cases y with
          | inl b => exact L.proper a b h
          | inr b => exact False.elim h
      | inr a =>
        cases y with
        | none => exact False.elim h
        | some y =>
          cases y with
          | inl b => exact False.elim h
          | inr b => exact R.proper a b h
  have hcard' : ∀ x, (C x).card = t := by
    intro x
    cases x with
    | none => exact hX
    | some x => cases x with
      | inl a => exact L.color_card a
      | inr b => exact R.color_card b
  have hleft : ∀ a b, G.Adj (some (Sum.inl a)) (some (Sum.inl b)) → L.side a ≠ L.side b :=
    fun a b h => L.bipartite a b h
  have hright : ∀ a b, G.Adj (some (Sum.inr a)) (some (Sum.inr b)) → R.side a ≠ R.side b :=
    fun a b h => R.bipartite a b h
  have hcross : ∀ a b, ¬ G.Adj (some (Sum.inl a)) (some (Sum.inr b)) := fun _ _ h => h
  have hnewright : ∀ b, ¬ G.Adj none (some (Sum.inr b)) := fun _ h => h
  have hnewleft : ∀ a, G.Adj none (some (Sum.inl a)) ↔ L.side a = true := fun _ => Iff.rfl
  obtain ⟨flip, target, hside, hlarge⟩ := op869_bipartite_gadget_growth G C L.side R.side
    (t+j*((t+1)/2)) t hleft hright hcross hnewright hnewleft hproper hX L.large R.large
  let side : Option (α ⊕ β) → Bool := fun v => decide (op869_gadget_side L.side R.side flip v = target)
  have hside' : ∀ x y, G.Adj x y → side x ≠ side y := by
    intro x y h
    have hxy := hside x y h
    dsimp [side]
    cases hx : op869_gadget_side L.side R.side flip x <;>
      cases hy : op869_gadget_side L.side R.side flip y <;>
      cases target <;> simp_all
  have hlarge' : t+(j+1)*((t+1)/2) ≤ ((Finset.univ.filter (fun v => side v = true)).biUnion C).card := by
    have heq : t+(j+1)*((t+1)/2) = (t+j*((t+1)/2))+(t+1)/2 := by ring
    rw [heq]
    simpa [side] using hlarge
  have hsize : Fintype.card (Option (α ⊕ β)) ≤ 2^((j+1)+1)-1 := by
    have hL := L.size
    have hR := R.size
    have hp : 0 < 2^(j+1) := by positivity
    have heq : 2^((j+1)+1) = 2^(j+1)*2 := by rw [pow_succ]
    simp only [Fintype.card_option, Fintype.card_sum]
    omega
  exact ⟨{ color_card := hcard', proper := hproper, side := side, bipartite := hside', large := hlarge', size := hsize }⟩

theorem op869_gadget_recursive_base {γ : Type} [DecidableEq γ] (t : ℕ)
    (X : Finset γ) (hX : X.card = t) :
    Nonempty (Op869GadgetCert (⊥ : SimpleGraph Unit) (fun _ => X) t 0) := by
  classical
  refine ⟨{ color_card := fun _ => hX, proper := ?_, side := fun _ => true, bipartite := ?_, large := ?_, size := ?_ }⟩
  · simp
  · simp
  · simpa [hX]
  · simp

/-- Finite-board induction move for the one-sided bipartite gadget. -/
theorem op869_board_two_copies_amplify {n m : ℕ} (offset : ℕ) (h : offset+n ≤ m)
    (baseP : Fin m → Finset (Fin m)) (baseC : Fin m → Finset ℕ)
    (P : Fin n → Finset (Fin n)) (C : Fin n → Finset ℕ)
    (baseSide : Fin m → Bool) (localSide : Fin n → Bool)
    (i a t : ℕ) (hi : i ≤ n) (hr : offset+i < m)
    (hbaseClear : ∀ x, offset ≤ x.val → baseP x = ∅)
    (hlocalClear : ∀ x, i ≤ x.val → P x = ∅)
    (hbaseSide : ∀ x y, (op869_graph_from_predecessors baseP).Adj x y → baseSide x ≠ baseSide y)
    (hlocalSide : ∀ x y, (op869_graph_from_predecessors P).Adj x y → localSide x ≠ localSide y)
    (S : Finset (Fin m)) (hSbefore : ∀ x ∈ S, x.val < offset)
    (hSside : ∀ x ∈ S, baseSide x = true)
    (X : Finset ℕ) (hX : X.card = t)
    (hvalid : ∀ x ∈ S, Disjoint (op869_splice_colors offset h baseC C x) X)
    (hfirst : a ≤ (S.biUnion (op869_splice_colors offset h baseC C)).card)
    (hsecond : a ≤ (((Finset.univ.filter (fun x : Fin n => x.val < i ∧ localSide x = true)).map
      (op869_offset_emb offset h)).biUnion (op869_splice_colors offset h baseC C)).card) :
    let root : Fin m := ⟨offset+i, hr⟩
    let P₀ := op869_splice_preds offset h baseP (fun _ => ∅) P
    let C₀ := op869_splice_colors offset h baseC C
    let P₁ := Function.update P₀ root S
    let C₁ := Function.update C₀ root X
    ∃ side : Fin m → Bool,
      (∀ x y, (op869_graph_from_predecessors P₁).Adj x y → side x ≠ side y) ∧
      a+(t+1)/2 ≤ ((Finset.univ.filter (fun x : Fin m =>
        x.val ≤ root.val ∧ side x = true)).biUnion C₁).card := by
  classical
  let root : Fin m := ⟨offset+i, hr⟩
  let P₀ := op869_splice_preds offset h baseP (fun _ => ∅) P
  let C₀ := op869_splice_colors offset h baseC C
  let P₁ := Function.update P₀ root S
  let C₁ := Function.update C₀ root X
  let L := (Finset.univ.filter (fun x : Fin n => x.val < i ∧ localSide x = true))
  let T := L.map (op869_offset_emb offset h)
  let A := S.biUnion C₀
  let B := T.biUnion C₀
  change ∃ side : Fin m → Bool,
      (∀ x y, (op869_graph_from_predecessors P₁).Adj x y → side x ≠ side y) ∧
      a+(t+1)/2 ≤ ((Finset.univ.filter (fun x : Fin m =>
        x.val ≤ root.val ∧ side x = true)).biUnion C₁).card
  have hSroot : ∀ x ∈ S, x < root := by
    intro x hx
    have hb := hSbefore x hx
    change x.val < offset+i
    omega
  have hclear : ∀ x, root.val ≤ x.val → P₀ x = ∅ := by
    intro x hx
    apply op869_spliced_future_predecessors_empty offset h baseP P i hbaseClear hlocalClear
    exact hx
  have hflip : ∀ x y, (op869_graph_from_predecessors P).Adj x y → (!localSide x) ≠ (!localSide y) := by
    intro x y hxy
    have hd := hlocalSide x y hxy
    cases hx : localSide x <;> cases hy : localSide y <;> simp_all
  obtain ⟨same, hsameOutside, hsameInside, hsameProper⟩ :=
    op869_disjoint_splice_bipartition offset h baseP P baseSide localSide hbaseClear hbaseSide hlocalSide
  obtain ⟨flip, hflipOutside, hflipInside, hflipProper⟩ :=
    op869_disjoint_splice_bipartition offset h baseP P baseSide (fun x => !localSide x) hbaseClear hbaseSide hflip
  have hsameS : ∀ x ∈ S, same x = true := by
    intro x hx
    rw [hsameOutside x (by have := hSbefore x hx; omega)]
    exact hSside x hx
  have hflipS : ∀ x ∈ S, flip x = true := by
    intro x hx
    rw [hflipOutside x (by have := hSbefore x hx; omega)]
    exact hSside x hx
  obtain ⟨sameR, hsameUnchanged, hsameRoot, hsameRootProper⟩ :=
    op869_add_root_to_bipartition P₀ root S same hclear hSroot hsameProper hsameS
  obtain ⟨flipR, hflipUnchanged, hflipRoot, hflipRootProper⟩ :=
    op869_add_root_to_bipartition P₀ root S flip hclear hSroot hflipProper hflipS
  have hdis : Disjoint X A := by
    apply Finset.disjoint_left.mpr
    intro c hc hca
    obtain ⟨x,hx,hcx⟩ := Finset.mem_biUnion.mp hca
    exact Finset.disjoint_left.mp (hvalid x hx) hcx hc
  have hgrow := op869_color_set_amplification A B X a t hfirst hsecond hX hdis
  have htrue : A ∪ B ⊆ ((Finset.univ.filter (fun x : Fin m =>
      x.val ≤ root.val ∧ sameR x = true)).biUnion C₁) := by
    intro c hc
    rcases Finset.mem_union.mp hc with hc | hc
    · obtain ⟨x,hx,hcx⟩ := Finset.mem_biUnion.mp hc
      have hxr : x < root := hSroot x hx
      have hxne : x ≠ root := ne_of_lt hxr
      apply Finset.mem_biUnion.mpr
      refine ⟨x, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨le_of_lt hxr, by rw [hsameUnchanged x hxne]; exact hsameS x hx⟩
      · simpa [C₁, Function.update_of_ne hxne] using hcx
    · obtain ⟨x,hx,hcx⟩ := Finset.mem_biUnion.mp hc
      obtain ⟨y,hy,rfl⟩ := Finset.mem_map.mp hx
      have hy' : y.val < i ∧ localSide y = true := (Finset.mem_filter.mp hy).2
      have hxr : op869_offset_emb offset h y < root := by
        change offset+y.val < offset+i
        omega
      have hxne : op869_offset_emb offset h y ≠ root := ne_of_lt hxr
      apply Finset.mem_biUnion.mpr
      refine ⟨op869_offset_emb offset h y, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨le_of_lt hxr, by rw [hsameUnchanged _ hxne, hsameInside y]; exact hy'.2⟩
      · simpa [C₁, Function.update_of_ne hxne] using hcx
  have hfalse : B ∪ X ⊆ ((Finset.univ.filter (fun x : Fin m =>
      x.val ≤ root.val ∧ (!flipR x) = true)).biUnion C₁) := by
    intro c hc
    rcases Finset.mem_union.mp hc with hc | hc
    · obtain ⟨x,hx,hcx⟩ := Finset.mem_biUnion.mp hc
      obtain ⟨y,hy,rfl⟩ := Finset.mem_map.mp hx
      have hy' : y.val < i ∧ localSide y = true := (Finset.mem_filter.mp hy).2
      have hxr : op869_offset_emb offset h y < root := by
        change offset+y.val < offset+i
        omega
      have hxne : op869_offset_emb offset h y ≠ root := ne_of_lt hxr
      apply Finset.mem_biUnion.mpr
      refine ⟨op869_offset_emb offset h y, ?_, ?_⟩
      · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
        refine ⟨le_of_lt hxr, ?_⟩
        rw [hflipUnchanged _ hxne, hflipInside y, hy'.2]
        rfl
      · simpa [C₁, Function.update_of_ne hxne] using hcx
    · apply Finset.mem_biUnion.mpr
      refine ⟨root, ?_, ?_⟩
      · simp [hflipRoot]
      · simpa [C₁] using hc
  rcases hgrow with hAB | hBX
  · exact ⟨sameR, hsameRootProper, le_trans hAB (Finset.card_le_card htrue)⟩
  · refine ⟨fun x => !flipR x, ?_, le_trans hBX (Finset.card_le_card hfalse)⟩
    intro x y hxy
    have hd := hflipRootProper x y hxy
    cases hx : flipR x <;> cases hy : flipR y <;> simp_all
