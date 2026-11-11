import AFTD.Prelude
import AFTD.Kb.Tcs.BipartiteSubsetStandardListColorable
import AFTD.Kb.Tcs.BipartiteSubsetGraph
import AFTD.Kb.Tcs.G

/-!
# bipartite_subset_colorable_succ

Topic: graphs   Node: d15555828e72

Provenance: helper lemma. Two-new-colors lifting construction for OP-861 in arXiv:2610.42094.

For every positive k and threshold r, colorability of the standard-list subset graph at k implies colorability at k+1 and the same threshold.
-/

def op861_selectors (α : Type) [DecidableEq α] (k r : ℕ) : Prop :=
  ∃ f g : {S : Finset α // S.card = k} → α,
    (∀ S, f S ∈ S.1) ∧ (∀ S, g S ∈ S.1) ∧
    (∀ S T, (S.1 ∩ T.1).card ≤ r → f S ≠ g T)

theorem op861_selector_lift_aux (α : Type) [DecidableEq α] (k r : ℕ)
    (h : op861_selectors α k r) : op861_selectors (α ⊕ Fin 2) (k+1) r := by
  classical
  obtain ⟨f, g, hf, hg, hfg⟩ := h
  let Old (S : {S : Finset (α ⊕ Fin 2) // S.card = k+1})
      (hn : ¬ (Sum.inr (0 : Fin 2) ∈ S.1 ∧ Sum.inr (1 : Fin 2) ∈ S.1)) :
      {U : Finset α // U.card = k ∧ U ⊆ S.1.toLeft} := by
    have hne : S.1.toRight ≠ (Finset.univ : Finset (Fin 2)) := by
      intro heq
      apply hn
      constructor <;> apply Finset.mem_toRight.mp <;> rw [heq] <;> simp
    have hlt : S.1.toRight.card < 2 := by
      have hh := Finset.card_lt_card (Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ _, hne⟩)
      simpa using hh
    have hsum := S.1.card_toLeft_add_card_toRight
    have hsize := S.2
    have hle : k ≤ S.1.toLeft.card := by omega
    let U := Classical.choose (Finset.exists_subset_card_eq hle)
    have hU := Classical.choose_spec (Finset.exists_subset_card_eq hle)
    exact ⟨U, hU.2, hU.1⟩
  let L (S : {S : Finset (α ⊕ Fin 2) // S.card = k+1}) : α ⊕ Fin 2 :=
    if hn : Sum.inr (0 : Fin 2) ∈ S.1 ∧ Sum.inr (1 : Fin 2) ∈ S.1 then
      Sum.inr 0
    else Sum.inl (f ⟨(Old S hn).1, (Old S hn).2.1⟩)
  let R (S : {S : Finset (α ⊕ Fin 2) // S.card = k+1}) : α ⊕ Fin 2 :=
    if hn : Sum.inr (0 : Fin 2) ∈ S.1 ∧ Sum.inr (1 : Fin 2) ∈ S.1 then
      Sum.inr 1
    else Sum.inl (g ⟨(Old S hn).1, (Old S hn).2.1⟩)
  refine ⟨L, R, ?_, ?_, ?_⟩
  · intro S
    by_cases hn : Sum.inr (0 : Fin 2) ∈ S.1 ∧ Sum.inr (1 : Fin 2) ∈ S.1
    · simpa [L, hn] using hn.1
    · simp only [L, dif_neg hn]
      exact Finset.mem_toLeft.mp ((Old S hn).2.2 (hf ⟨(Old S hn).1, (Old S hn).2.1⟩))
  · intro S
    by_cases hn : Sum.inr (0 : Fin 2) ∈ S.1 ∧ Sum.inr (1 : Fin 2) ∈ S.1
    · simpa [R, hn] using hn.2
    · simp only [R, dif_neg hn]
      exact Finset.mem_toLeft.mp ((Old S hn).2.2 (hg ⟨(Old S hn).1, (Old S hn).2.1⟩))
  · intro S T hadj heq
    by_cases hs : Sum.inr (0 : Fin 2) ∈ S.1 ∧ Sum.inr (1 : Fin 2) ∈ S.1
    · by_cases ht : Sum.inr (0 : Fin 2) ∈ T.1 ∧ Sum.inr (1 : Fin 2) ∈ T.1
      · simp [L, R, hs, ht] at heq
      · simp [L, R, hs, ht] at heq
    · by_cases ht : Sum.inr (0 : Fin 2) ∈ T.1 ∧ Sum.inr (1 : Fin 2) ∈ T.1
      · simp [L, R, hs, ht] at heq
      · have hsub : ((Old S hs).1 ∩ (Old T ht).1).map (Function.Embedding.inl : α ↪ α ⊕ Fin 2) ⊆ S.1 ∩ T.1 := by
          intro x hx
          simp only [Finset.mem_map, Finset.mem_inter] at hx ⊢
          obtain ⟨a, ⟨ha, hb⟩, rfl⟩ := hx
          exact ⟨Finset.mem_toLeft.mp ((Old S hs).2.2 ha), Finset.mem_toLeft.mp ((Old T ht).2.2 hb)⟩
        have hcard := Finset.card_le_card hsub
        rw [Finset.card_map] at hcard
        have hsmall : ((Old S hs).1 ∩ (Old T ht).1).card ≤ r := le_trans hcard hadj
        have hneq := hfg ⟨(Old S hs).1, (Old S hs).2.1⟩ ⟨(Old T ht).1, (Old T ht).2.1⟩ hsmall
        exact hneq (by simpa [L, R, hs, ht] using heq)


theorem op861_selectors_equiv {α β : Type} [DecidableEq α] [DecidableEq β]
    (e : α ≃ β) (k r : ℕ) (h : op861_selectors α k r) : op861_selectors β k r := by
  classical
  obtain ⟨f, g, hf, hg, hfg⟩ := h
  let old (S : {S : Finset β // S.card = k}) : {S : Finset α // S.card = k} :=
    ⟨S.1.map e.symm.toEmbedding, by simpa using S.2⟩
  refine ⟨fun S => e (f (old S)), fun S => e (g (old S)), ?_, ?_, ?_⟩
  · intro S
    have hh := hf (old S)
    simp only [old, Finset.mem_map] at hh
    obtain ⟨b, hb, heq⟩ := hh
    change e.symm b = f (old S) at heq
    change e (f (old S)) ∈ S.1
    have hvalue : e (f (old S)) = b := by rw [← heq]; simp
    rw [hvalue]
    exact hb
  · intro S
    have hh := hg (old S)
    simp only [old, Finset.mem_map] at hh
    obtain ⟨b, hb, heq⟩ := hh
    change e.symm b = g (old S) at heq
    change e (g (old S)) ∈ S.1
    have hvalue : e (g (old S)) = b := by rw [← heq]; simp
    rw [hvalue]
    exact hb
  · intro S T hadj heq
    have hs : ((old S).1 ∩ (old T).1).card ≤ r := by
      change ((S.1.map e.symm.toEmbedding) ∩ (T.1.map e.symm.toEmbedding)).card ≤ r
      rw [← Finset.map_inter, Finset.card_map]
      exact hadj
    exact (hfg (old S) (old T) hs) (e.injective heq)

theorem op861_selectors_graph (k r : ℕ) :
    op861_selectors (Fin (2*k-1)) k r ↔ bipartite_subset_standard_list_colorable k r := by
  classical
  constructor
  · rintro ⟨f, g, hf, hg, hfg⟩
    let col : ({S : Finset (Fin (2*k-1)) // S.card = k} ⊕
        {T : Finset (Fin (2*k-1)) // T.card = k}) → Fin (2*k-1) := Sum.elim f g
    have hv : ∀ {v w}, (bipartite_subset_graph k r).Adj v w → col v ≠ col w := by
      intro v w hv
      cases v with
      | inl S =>
        cases w with
        | inl T => exact False.elim hv
        | inr T => exact hfg S T hv
      | inr T =>
        cases w with
        | inl S => exact (hfg S T hv).symm
        | inr U => exact False.elim hv
    let C : (bipartite_subset_graph k r).Coloring (Fin (2*k-1)) := SimpleGraph.Coloring.mk col hv
    refine ⟨C, ?_⟩
    intro v
    cases v with
    | inl S => exact hf S
    | inr T => exact hg T
  · rintro ⟨C, hC⟩
    refine ⟨fun S => C (Sum.inl S), fun T => C (Sum.inr T), ?_, ?_, ?_⟩
    · intro S
      exact hC (Sum.inl S)
    · intro T
      exact hC (Sum.inr T)
    · intro S T hadj
      exact C.valid hadj

theorem bipartite_subset_colorable_succ (k r : ℕ) (hk : 1 ≤ k) : bipartite_subset_standard_list_colorable k r → bipartite_subset_standard_list_colorable (k+1) r := by
  intro h
  have hsel := (op861_selectors_graph k r).2 h
  have hlift := op861_selector_lift_aux (Fin (2*k-1)) k r hsel
  have heq : (2*k-1) + 2 = 2*(k+1)-1 := by omega
  let e : Fin (2*k-1) ⊕ Fin 2 ≃ Fin (2*(k+1)-1) :=
    finSumFinEquiv.trans (finCongr heq)
  have hnew := op861_selectors_equiv e (k+1) r hlift
  exact (op861_selectors_graph (k+1) r).1 hnew
