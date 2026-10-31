import AFTD.Prelude
import AFTD.Kb.Tcs.Graph11
import AFTD.Kb.Tcs.Graph11Diam
import AFTD.Kb.Tcs.Graph11ChromaticNumber
import AFTD.Kb.Tcs.Graph11NotIsMutualVisibilityColorableTwo
import AFTD.Kb.Tcs.GraphMutualVisibilityChromaticNumberLeChromaticNumberOfDiamTwo
import AFTD.Kb.Tcs.GraphIsMutualVisibilityColorable
import AFTD.Kb.Tcs.GraphIsMutualVisibilitySet
import AFTD.Kb.Tcs.GraphMutualVisibilityChromaticNumber

/-!
# graph_11_mutual_visibility_chromatic_number_eq_three

Topic: graphs   Node: 13f7697126a3

Provenance: formalization of a published result. Source: arXiv:2610.39430 Theorem 3.4

The simple graph G_11 has mutual-visibility chromatic number 3, chromatic number 3, and diameter 2.
-/

lemma graph_11_mutual_visibility_chromatic_number_eq_three_empty_is_mutual_visibility_set
    {V : Type*} (G : SimpleGraph V) :
    graph_is_mutual_visibility_set G ∅ := by
  intro u hu
  exact False.elim hu

lemma graph_11_mutual_visibility_chromatic_number_eq_three_colorable_mono
    {V : Type*} (G : SimpleGraph V) {n m : ℕ} (hnm : n ≤ m)
    (hc : graph_is_mutual_visibility_colorable G n) :
    graph_is_mutual_visibility_colorable G m := by
  obtain ⟨c, hc⟩ := hc
  let emb : Fin n ↪ Fin m := (Fin.castLEOrderEmb hnm).toEmbedding
  use fun v => emb (c v)
  intro i
  by_cases hi : ∃ j : Fin n, emb j = i
  · rcases hi with ⟨j, rfl⟩
    have : {v | emb (c v) = emb j} = {v | c v = j} := by
      ext v
      simp [emb.injective.eq_iff]
    rw [this]
    exact hc j
  · have : {v | emb (c v) = i} = ∅ := by
      ext v
      simp only [Set.mem_empty_iff_false, iff_false]
      intro h_eq
      exact hi ⟨c v, h_eq⟩
    rw [this]
    exact graph_11_mutual_visibility_chromatic_number_eq_three_empty_is_mutual_visibility_set G

/-- The mutual-visibility chromatic number of G_11 is 3. -/
theorem graph_11_mutual_visibility_chromatic_number_eq_three :
    graph_mutual_visibility_chromatic_number graph_11 = 3 ∧
    graph_11.chromaticNumber = 3 ∧
    graph_11.diam = 2 := by
  refine ⟨?_, graph_11_chromatic_number, graph_11_diam⟩
  have hle : graph_mutual_visibility_chromatic_number graph_11 ≤ 3 := by
    have h := graph_mutual_visibility_chromatic_number_le_chromatic_number_of_diam_two graph_11 graph_11_diam
    rw [graph_11_chromatic_number] at h
    exact h
  have hge : (3 : ℕ∞) ≤ graph_mutual_visibility_chromatic_number graph_11 := by
    dsimp [graph_mutual_visibility_chromatic_number]
    apply le_iInf
    intro n
    apply le_iInf
    intro hn
    change graph_is_mutual_visibility_colorable graph_11 n at hn
    by_contra! hlt
    have hle2 : n ≤ 2 := by
      norm_cast at hlt
      omega
    have h2 : graph_is_mutual_visibility_colorable graph_11 2 :=
      graph_11_mutual_visibility_chromatic_number_eq_three_colorable_mono graph_11 hle2 hn
    exact graph_11_not_is_mutual_visibility_colorable_two h2
  exact le_antisymm hle hge
