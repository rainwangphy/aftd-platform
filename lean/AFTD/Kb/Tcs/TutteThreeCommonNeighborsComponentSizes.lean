import AFTD.Prelude

/-!
# tutte_three_common_neighbors_component_sizes

Topic: graphs   Node: ed0b5eef5f62

Provenance: helper lemma. OP-1957 codegree-three Tutte case: arithmetic classification of extra odd components.

If t is between one and three and t odd positive component sizes total at most three with each size plus t at least four, then t=1 and the sole size is three, or t=3 and all sizes are one.
-/

theorem tutte_three_common_neighbors_component_sizes (t : ℕ) (ht1 : 1 ≤ t) (ht3 : t ≤ 3)
    (f : Fin t → ℕ) (hodd : ∀ i, Odd (f i)) (hdeg : ∀ i, 4 ≤ t + f i)
    (hsum : (∑ i, f i) ≤ 3) :
    (t = 1 ∧ ∀ i, f i = 3) ∨ (t = 3 ∧ ∀ i, f i = 1) := by
  have hpos : ∀ i, 1 ≤ f i := by
    intro i
    obtain ⟨a,ha⟩ := hodd i
    omega
  interval_cases t
  · left
    constructor
    · rfl
    · intro i
      fin_cases i
      change f 0 = 3
      have hd := hdeg 0
      simp only [Fin.sum_univ_one] at hsum
      omega
  · have h0 := hdeg 0
    have h1 := hdeg 1
    obtain ⟨a,ha⟩ := hodd 0
    obtain ⟨b,hb⟩ := hodd 1
    simp only [Fin.sum_univ_two] at hsum
    omega
  · right
    constructor
    · rfl
    · intro i
      have h0 := hpos 0
      have h1 := hpos 1
      have h2 := hpos 2
      simp only [Fin.sum_univ_three] at hsum
      fin_cases i
      · change f 0 = 1; omega
      · change f 1 = 1; omega
      · change f 2 = 1; omega
