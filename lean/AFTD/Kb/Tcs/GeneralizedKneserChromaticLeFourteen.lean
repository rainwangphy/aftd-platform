import AFTD.Prelude
import AFTD.Kb.Tcs.GeneralizedKneserGraph
import AFTD.Kb.Tcs.GeneralizedKneserGraphAdj

/-!
# generalized_kneser_chromatic_le_fourteen

Topic: graphs   Node: 6ad09ccdf0b3

Provenance: formalization of a published result. Source: arXiv:2611.04486 Sec. 1 and Sec. 4.1

For every natural number n ≥ 4, the chromatic number of the generalized Kneser graph KG(2n, n, 3) is at most 14.
-/

def generalized_kneser_chromatic_le_fourteen_fanoLines : Fin 7 → Finset (Fin 7)
  | 0 => {0, 1, 2}
  | 1 => {0, 3, 4}
  | 2 => {0, 5, 6}
  | 3 => {1, 3, 5}
  | 4 => {1, 4, 6}
  | 5 => {2, 3, 6}
  | 6 => {2, 4, 5}

theorem generalized_kneser_chromatic_le_fourteen_card_fanoLines (i : Fin 7) :
    (generalized_kneser_chromatic_le_fourteen_fanoLines i).card = 3 := by
  fin_cases i <;> decide

theorem generalized_kneser_chromatic_le_fourteen_fano_monochromatic :
    ∀ S : Finset (Fin 7),
      (∃ i : Fin 7, generalized_kneser_chromatic_le_fourteen_fanoLines i ⊆ S) ∨
      (∃ i : Fin 7, ∀ x ∈ generalized_kneser_chromatic_le_fourteen_fanoLines i, x ∉ S) := by
  decide

def generalized_kneser_chromatic_le_fourteen_fanoEmb (n : ℕ) (_hn : 4 ≤ n) : Fin 7 ↪ Fin (2 * n) :=
  Fin.castLEEmb (by omega)

def generalized_kneser_chromatic_le_fourteen_fanoLineEmb (n : ℕ) (hn : 4 ≤ n) (i : Fin 7) :
    Finset (Fin (2 * n)) :=
  (generalized_kneser_chromatic_le_fourteen_fanoLines i).map
    (generalized_kneser_chromatic_le_fourteen_fanoEmb n hn)

theorem generalized_kneser_chromatic_le_fourteen_card_fanoLineEmb (n : ℕ) (hn : 4 ≤ n) (i : Fin 7) :
    (generalized_kneser_chromatic_le_fourteen_fanoLineEmb n hn i).card = 3 := by
  rw [generalized_kneser_chromatic_le_fourteen_fanoLineEmb, Finset.card_map,
    generalized_kneser_chromatic_le_fourteen_card_fanoLines]

def generalized_kneser_chromatic_le_fourteen_fanoRestrict (n : ℕ) (hn : 4 ≤ n)
    (s : Finset (Fin (2 * n))) : Finset (Fin 7) :=
  Finset.univ.filter (fun x => generalized_kneser_chromatic_le_fourteen_fanoEmb n hn x ∈ s)

theorem generalized_kneser_chromatic_le_fourteen_fanoLineEmb_subset_iff (n : ℕ) (hn : 4 ≤ n)
    (i : Fin 7) (s : Finset (Fin (2 * n))) :
    generalized_kneser_chromatic_le_fourteen_fanoLineEmb n hn i ⊆ s ↔
      generalized_kneser_chromatic_le_fourteen_fanoLines i ⊆
        generalized_kneser_chromatic_le_fourteen_fanoRestrict n hn s := by
  simp [generalized_kneser_chromatic_le_fourteen_fanoLineEmb,
    generalized_kneser_chromatic_le_fourteen_fanoRestrict, Finset.subset_iff]

theorem generalized_kneser_chromatic_le_fourteen_fanoLineEmb_disjoint_iff (n : ℕ) (hn : 4 ≤ n)
    (i : Fin 7) (s : Finset (Fin (2 * n))) :
    Disjoint (generalized_kneser_chromatic_le_fourteen_fanoLineEmb n hn i) s ↔
      ∀ x ∈ generalized_kneser_chromatic_le_fourteen_fanoLines i,
        x ∉ generalized_kneser_chromatic_le_fourteen_fanoRestrict n hn s := by
  simp [generalized_kneser_chromatic_le_fourteen_fanoLineEmb,
    generalized_kneser_chromatic_le_fourteen_fanoRestrict, Finset.disjoint_left]

def generalized_kneser_chromatic_le_fourteen_fanoValidColor (n : ℕ) (hn : 4 ≤ n)
    (s : Finset (Fin (2 * n))) (c : Fin 7 × Bool) : Prop :=
  if c.2 then
    generalized_kneser_chromatic_le_fourteen_fanoLineEmb n hn c.1 ⊆ s
  else
    Disjoint (generalized_kneser_chromatic_le_fourteen_fanoLineEmb n hn c.1) s

theorem generalized_kneser_chromatic_le_fourteen_exists_fanoValidColor (n : ℕ) (hn : 4 ≤ n)
    (s : Finset (Fin (2 * n))) :
    ∃ c : Fin 7 × Bool, generalized_kneser_chromatic_le_fourteen_fanoValidColor n hn s c := by
  rcases generalized_kneser_chromatic_le_fourteen_fano_monochromatic
    (generalized_kneser_chromatic_le_fourteen_fanoRestrict n hn s) with ⟨i, hi⟩ | ⟨i, hi⟩
  · use (i, true)
    dsimp [generalized_kneser_chromatic_le_fourteen_fanoValidColor]
    rwa [generalized_kneser_chromatic_le_fourteen_fanoLineEmb_subset_iff]
  · use (i, false)
    dsimp [generalized_kneser_chromatic_le_fourteen_fanoValidColor]
    rwa [generalized_kneser_chromatic_le_fourteen_fanoLineEmb_disjoint_iff]

noncomputable def generalized_kneser_chromatic_le_fourteen_fanoColor (n : ℕ) (hn : 4 ≤ n)
    (s : {s : Finset (Fin (2 * n)) // s.card = n}) : Fin 7 × Bool :=
  Classical.choose (generalized_kneser_chromatic_le_fourteen_exists_fanoValidColor n hn s.1)

theorem generalized_kneser_chromatic_le_fourteen_fanoColor_spec (n : ℕ) (hn : 4 ≤ n)
    (s : {s : Finset (Fin (2 * n)) // s.card = n}) :
    generalized_kneser_chromatic_le_fourteen_fanoValidColor n hn s.1
      (generalized_kneser_chromatic_le_fourteen_fanoColor n hn s) :=
  Classical.choose_spec (generalized_kneser_chromatic_le_fourteen_exists_fanoValidColor n hn s.1)

noncomputable def generalized_kneser_chromatic_le_fourteen_kneserColoring (n : ℕ) (hn : 4 ≤ n) :
    (generalized_kneser_graph n 3).Coloring (Fin 7 × Bool) :=
  SimpleGraph.Coloring.mk (generalized_kneser_chromatic_le_fourteen_fanoColor n hn) (by
    intro s t hadj h_eq
    have h_lt : (s.1 ∩ t.1).card < 3 := by
      have := (generalized_kneser_graph_adj n 3 s t).mp hadj
      exact this.2
    have hs_spec := generalized_kneser_chromatic_le_fourteen_fanoColor_spec n hn s
    have ht_spec := generalized_kneser_chromatic_le_fourteen_fanoColor_spec n hn t
    rw [h_eq] at hs_spec
    set c := generalized_kneser_chromatic_le_fourteen_fanoColor n hn t
    dsimp [generalized_kneser_chromatic_le_fourteen_fanoValidColor] at hs_spec ht_spec
    set L := generalized_kneser_chromatic_le_fourteen_fanoLineEmb n hn c.1
    have hL : L.card = 3 := generalized_kneser_chromatic_le_fourteen_card_fanoLineEmb n hn c.1
    by_cases hc2 : c.2
    · rw [if_pos hc2] at hs_spec ht_spec
      have h_sub : L ⊆ s.1 ∩ t.1 := Finset.subset_inter hs_spec ht_spec
      have h3 : 3 ≤ (s.1 ∩ t.1).card := by
        have := Finset.card_le_card h_sub
        rwa [hL] at this
      omega
    · rw [if_neg hc2] at hs_spec ht_spec
      have hd_union : Disjoint L (s.1 ∪ t.1) :=
        Finset.disjoint_union_right.mpr ⟨hs_spec, ht_spec⟩
      have h_sub : L ∪ (s.1 ∪ t.1) ⊆ Finset.univ := Finset.subset_univ _
      have h_card_le : (L ∪ (s.1 ∪ t.1)).card ≤ 2 * n := by
        have := Finset.card_le_card h_sub
        rwa [Finset.card_univ, Fintype.card_fin] at this
      have h_disj_card : (L ∪ (s.1 ∪ t.1)).card = L.card + (s.1 ∪ t.1).card :=
        Finset.card_union_of_disjoint hd_union
      rw [h_disj_card, hL] at h_card_le
      have h_inter : (s.1 ∪ t.1).card + (s.1 ∩ t.1).card = s.1.card + t.1.card :=
        Finset.card_union_add_card_inter s.1 t.1
      rw [s.2, t.2] at h_inter
      omega)

/-- For every n ≥ 4, the chromatic number of the generalized Kneser graph KG(2n, n, 3) is at most 14. -/
theorem generalized_kneser_chromatic_le_fourteen (n : ℕ) (hn : 4 ≤ n) :
    (generalized_kneser_graph n 3).chromaticNumber ≤ 14 := by
  have hc : (generalized_kneser_graph n 3).Colorable (Fintype.card (Fin 7 × Bool)) :=
    (generalized_kneser_chromatic_le_fourteen_kneserColoring n hn).colorable
  have h_card : Fintype.card (Fin 7 × Bool) = 14 := by decide
  rw [h_card] at hc
  exact hc.chromaticNumber_le
