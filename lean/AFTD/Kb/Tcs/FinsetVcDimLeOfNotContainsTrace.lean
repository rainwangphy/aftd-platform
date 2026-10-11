import AFTD.Prelude
import AFTD.Kb.Tcs.FinsetContainsTrace

/-!
# finset_vc_dim_le_of_not_contains_trace

Topic: combinatorics   Node: 9c10c10d6515

Provenance: formalization of a published result. Source: arXiv:2610.08151 (Polynomial-in-r bounds for forbidden traces of uniform hypergraphs), Proposition 1. VCdim is Mathlib's Finset.vcDim (largest shattered set).

Let H be a set system on an h-element ground set, h ≥ 1. If a finite set system F is trace-H-free, then VCdim(F) ≤ h − 1.
-/

theorem finset_vc_dim_le_of_not_contains_trace {α : Type*} [DecidableEq α] {h : ℕ} (hh : 1 ≤ h)
    (𝓗 : Finset (Finset (Fin h))) (𝓕 : Finset (Finset α))
    (hfree : ¬ finset_contains_trace 𝓕 𝓗) : 𝓕.vcDim ≤ h - 1 := by
  unfold Finset.vcDim
  refine Finset.sup_le fun s hs => ?_
  rw [Finset.mem_shatterer] at hs
  by_contra hlt
  rw [not_le] at hlt
  obtain ⟨t, hts, htc⟩ := Finset.exists_subset_card_eq (show h ≤ s.card by omega)
  have ht : 𝓕.Shatters t := hs.mono_right hts
  let φ : Fin h ↪ α :=
    (t.equivFinOfCardEq htc).symm.toEmbedding.trans (Function.Embedding.subtype _)
  have himg : Finset.univ.map φ = t := by
    ext x
    simp only [Finset.mem_map, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      exact ((t.equivFinOfCardEq htc).symm i).2
    · intro hx
      refine ⟨t.equivFinOfCardEq htc ⟨x, hx⟩, ?_⟩
      simp [φ]
  apply hfree
  refine ⟨φ, fun e _ => ?_⟩
  have hsub : e.map φ ⊆ t := by
    rw [← himg]
    exact Finset.map_subset_map.2 (Finset.subset_univ e)
  obtain ⟨u, hu, hut⟩ := ht hsub
  exact ⟨u, hu, by rw [himg, Finset.inter_comm]; exact hut⟩
