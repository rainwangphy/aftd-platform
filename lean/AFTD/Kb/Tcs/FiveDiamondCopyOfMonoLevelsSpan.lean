import AFTD.Prelude
import AFTD.Kb.Tcs.HasMonochromaticDiamondCopy
import AFTD.Kb.Tcs.ExistsFiveFinsetsCard

/-!
# five_diamond_copy_of_mono_levels_span

Topic: combinatorics   Node: e65cfaa8d3e9

Provenance: helper lemma. step towards five_diamond_ramsey_property_step

Generalised level-copy lemma: if col-coloured sets B ⊆ T straddle a completely col-monochromatic level m (|B| < m < |T|), and the middle layer of the interval [B,T] is wide enough, C(|T|-|B|, m-|B|) ≥ 5, then there is a monochromatic induced 5-diamond in colour col.
-/

/-- A col-monochromatic level strictly inside a col-coloured interval of width with C(width,·) ≥ 5 yields a monochromatic 5-diamond. -/
theorem five_diamond_copy_of_mono_levels_span {d k : ℕ} (χ : Finset (Fin d) → Fin k) (col : Fin k)
    (B T : Finset (Fin d)) (hBT : B ⊆ T) (hB : χ B = col) (hT : χ T = col)
    (m : ℕ) (hBm : B.card < m) (hmT : m < T.card)
    (hlev : ∀ M : Finset (Fin d), M.card = m → χ M = col)
    (hchoose : 5 ≤ Nat.choose (T.card - B.card) (m - B.card)) :
    has_monochromatic_diamond_copy 5 d col χ := by
  obtain ⟨S, hScard, hSne⟩ := exists_five_finsets_card
    (m := (T \ B).card) (r := m - B.card)
    (by rw [Finset.card_sdiff_of_subset hBT]; exact hchoose)
  let e := (Finset.equivFin (T \ B)).symm
  let f : Fin (T \ B).card ↪ Fin d :=
    e.toEmbedding.trans (Function.Embedding.subtype (fun x => x ∈ T \ B))
  let img : Fin 5 → Finset (Fin d) := fun i => Finset.map f (S i)
  let M : Fin 5 → Finset (Fin d) := fun i => B ∪ img i
  have h_img_sub : ∀ i, img i ⊆ T \ B := by
    intro i x hx
    change x ∈ Finset.map f (S i) at hx
    rw [Finset.mem_map] at hx
    obtain ⟨a, _, rfl⟩ := hx
    exact (e a).2
  have h_img_card : ∀ i, (img i).card = m - B.card := by
    intro i
    change (Finset.map f (S i)).card = m - B.card
    rw [Finset.card_map]
    exact hScard i
  have h_disj : ∀ i, Disjoint B (img i) := by
    intro i
    rw [Finset.disjoint_left]
    intro x hxB hximg
    exact (Finset.mem_sdiff.mp (h_img_sub i hximg)).2 hxB
  have hM_card : ∀ i, (M i).card = m := by
    intro i
    change (B ∪ img i).card = m
    rw [Finset.card_union_of_disjoint (h_disj i), h_img_card i]
    omega
  have hBT_ssub : B ⊂ T := by
    rw [Finset.ssubset_iff_subset_ne]
    exact ⟨hBT, by rintro rfl; omega⟩
  refine ⟨B, T, hBT_ssub, hB, hT, M, ?_, ?_⟩
  · intro i
    refine ⟨?_, ?_, hlev (M i) (hM_card i)⟩
    · rw [Finset.ssubset_iff_subset_ne]
      refine ⟨Finset.subset_union_left, ?_⟩
      intro h
      have h1 : B.card = (M i).card := congrArg Finset.card h
      rw [h1, hM_card i] at hBm
      exact Nat.lt_irrefl m hBm
    · rw [Finset.ssubset_iff_subset_ne]
      refine ⟨?_, ?_⟩
      · intro x hx
        change x ∈ B ∪ img i at hx
        rcases Finset.mem_union.mp hx with hxB | hximg
        · exact hBT hxB
        · exact (Finset.mem_sdiff.mp (h_img_sub i hximg)).1
      · intro h
        have h1 : (M i).card = T.card := congrArg Finset.card h
        rw [← h1, hM_card i] at hmT
        exact Nat.lt_irrefl m hmT
  · intro i i' hne hsub
    have hsub' : img i ⊆ img i' := by
      intro x hx
      have hxM : x ∈ M i := Finset.mem_union_right B hx
      have hxM' : x ∈ M i' := hsub hxM
      change x ∈ B ∪ img i' at hxM'
      rw [Finset.mem_union] at hxM'
      rcases hxM' with h | h
      · exact absurd hx (Finset.disjoint_left.mp (h_disj i) h)
      · exact h
    have himg_eq : img i = img i' :=
      Finset.eq_of_subset_of_card_le hsub' (by rw [h_img_card, h_img_card])
    exact hSne i i' hne (Finset.map_injective f himg_eq)
