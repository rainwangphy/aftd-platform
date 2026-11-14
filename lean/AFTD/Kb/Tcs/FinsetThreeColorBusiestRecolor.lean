import AFTD.Prelude

/-!
# finset_three_color_busiest_recolor

Topic: graphs   Node: 01782ab2580f

Provenance: helper lemma. Pigeonhole step in the exceptional-vertex reduction for OP-110.

Given three colors and a finite set excluding a distinguished point, recolor only that point so that at least one third of the set has its new color.
-/

theorem finset_three_color_busiest_recolor
    (α : Type) [Fintype α] [DecidableEq α] (col : α → Fin 3) (x : α) (M : Finset α)
    (hx : x ∉ M) :
    ∃ col' : α → Fin 3, (∀ v, v ≠ x → col' v = col v) ∧
      M.card ≤ 3 * (M.filter fun v => col' v = col' x).card := by
  classical
  let S : Fin 3 → Finset α := fun i => M.filter fun v => col v = i
  have hsum : M.card = (S 0).card+(S 1).card+(S 2).card := by
    have h := Finset.card_eq_sum_card_fiberwise (f := col) (s := M)
      (t := (Finset.univ : Finset (Fin 3))) (by simp)
    simp only [Fin.sum_univ_three] at h
    change M.card = (S 0).card + (S 1).card + (S 2).card at h
    exact h
  have hi : ∃ i : Fin 3, M.card ≤ 3 * (S i).card := by
    by_contra hn
    have h0 : 3*(S 0).card < M.card := by
      by_contra h; exact hn ⟨0, by omega⟩
    have h1 : 3*(S 1).card < M.card := by
      by_contra h; exact hn ⟨1, by omega⟩
    have h2 : 3*(S 2).card < M.card := by
      by_contra h; exact hn ⟨2, by omega⟩
    omega
  obtain ⟨i,hi⟩ := hi
  let col' : α → Fin 3 := fun v => if v = x then i else col v
  refine ⟨col', ?_, ?_⟩
  · intro v hv
    simp [col',hv]
  · have heq : (M.filter fun v => col' v = col' x) = S i := by
      ext v
      by_cases hv : v ∈ M
      · have hvx : v ≠ x := by intro h; subst v; exact hx hv
        simp [S,col',hv,hvx]
      · simp [S,hv]
    rw [heq]
    exact hi
