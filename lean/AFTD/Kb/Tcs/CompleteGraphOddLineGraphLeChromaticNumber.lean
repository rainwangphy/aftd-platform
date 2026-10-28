import AFTD.Prelude
import AFTD.Kb.Tcs.WildNumberCompleteGraphMinProperColoringGe

/-!
# complete_graph_odd_line_graph_le_chromaticNumber

Topic: graphs   Node: 027fc2afd198

Provenance: helper lemma. step towards complete_graph_odd_line_graph_chromatic_number_eq

For odd n ≥ 3, the chromatic number of the line graph of K_n is at least n.
-/

/-- For odd n ≥ 3, the chromatic number of the line graph of K_n is at least n. -/
theorem complete_graph_odd_line_graph_le_chromaticNumber (n : ℕ) (hn : 3 ≤ n) (hodd : n % 2 = 1) : n ≤ (⊤ : SimpleGraph (Fin n)).lineGraph.chromaticNumber := by
  classical
  rw [SimpleGraph.le_chromaticNumber_iff_coloring]
  intro k c
  let v : Fin n := ⟨0, by omega⟩
  have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  let i0 := c ⟨s(⟨0, by omega⟩, ⟨1, by omega⟩), wild_kn_mem h01⟩
  let Cv := (Finset.univ.erase v).image (fun x => if h : v ≠ x then c ⟨s(v,x),wild_kn_mem h⟩ else i0)
  have hcard : Cv.card = n-1 := by
    dsimp only [Cv]
    rw [Finset.card_image_of_injOn, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin]
    intro a ha b hb hab
    have ha' := Ne.symm (Finset.ne_of_mem_erase ha)
    have hb' := Ne.symm (Finset.ne_of_mem_erase hb)
    simp only [dif_pos ha', dif_pos hb'] at hab
    exact wild_kn_same_color c ha' hb' hab
  obtain ⟨e, he⟩ := wild_kn_exists_missing_color_of_odd hn hodd c v
  have hmiss : c e ∉ Cv := by
    intro hi
    obtain ⟨x,hx,hcol⟩ := Finset.mem_image.1 hi
    have hvx : v ≠ x := Ne.symm (Finset.ne_of_mem_erase hx)
    simp only [dif_pos hvx] at hcol
    exact he x hvx hcol
  have hstrict : Cv ⊂ Finset.univ := Finset.ssubset_iff_subset_ne.2
    ⟨Finset.subset_univ _, fun h => hmiss (h ▸ Finset.mem_univ _)⟩
  have hi := Finset.card_lt_card hstrict
  rw [hcard, Finset.card_univ, Fintype.card_fin] at hi
  exact_mod_cast (show n ≤ k by omega)
