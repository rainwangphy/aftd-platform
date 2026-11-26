import AFTD.Prelude

/-!
# op874_two_color_palettes_repeat

Topic: graphs   Node: c946389d30bd

Provenance: helper lemma. Matching-adversarial factor-word construction for OP-874, https://arxiv.org/abs/2610.41950.

Any assignment of two-element subsets of four colors to at least seven vertices repeats a palette.
-/

theorem op874_two_color_palettes_repeat
    {V : Type*} [DecidableEq V] (S : Finset V) (P : V → Finset (Fin 4))
    (hP : ∀ v ∈ S, (P v).card = 2) (hS : 7 ≤ S.card) :
    ∃ u ∈ S, ∃ v ∈ S, u ≠ v ∧ P u = P v := by
  classical
  by_contra hn
  push Not at hn
  let Q : Finset (Finset (Fin 4)) := Finset.univ.filter fun p => p.card = 2
  have hQ : Q.card = 6 := by decide
  have hsub : S.image P ⊆ Q := by
    intro t ht
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp ht
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hP v hv⟩
  have hinj : Set.InjOn P S := by
    intro u hu v hv heq
    by_contra hne
    exact hn u hu v hv hne heq
  have himage : (S.image P).card = S.card := Finset.card_image_iff.mpr hinj
  have hle := Finset.card_le_card hsub
  omega
