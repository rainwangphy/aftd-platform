import AFTD.Prelude

/-!
# degree_list_kempe_step_symmetric

Topic: graphs   Node: 565074118281

Provenance: helper lemma. step towards three_connected_degree_list_kempe_quadratic_diameter

The degree-list Kempe step transition relation is symmetric: if c₂ is obtained from c₁ by an L-valid Kempe change swapping colors a and b on an induced connected component U, then c₁ is obtained from c₂ by an L-valid Kempe change swapping the same colors on the same component U.
-/

/-- The degree-list Kempe step transition relation is symmetric: swapping colors a and b on an induced connected component U is an involution. -/
theorem degree_list_kempe_step_symmetric {n : ℕ} (G : SimpleGraph (Fin n))
    {C : Type} [Fintype C] [DecidableEq C] (L : Fin n → Finset C)
    (c₁ c₂ : G.Coloring C)
    (hL₁ : ∀ v, c₁ v ∈ L v) (hL₂ : ∀ v, c₂ v ∈ L v)
    (a b : C) (U : Set (Fin n))
    (hab : a ≠ b) (hU_ne : U.Nonempty) (hU_colors : ∀ v ∈ U, c₁ v = a ∨ c₁ v = b)
    (hU_conn : (G.induce U).Connected)
    (hU_closed : ∀ u ∈ U, ∀ v : Fin n, G.Adj u v → (c₁ v = a ∨ c₁ v = b) → v ∈ U)
    (hc₂_in : ∀ v ∈ U, c₂ v = (if c₁ v = a then b else a))
    (hc₂_out : ∀ v ∉ U, c₂ v = c₁ v) :
    (∀ v, c₂ v ∈ L v) ∧ (∀ v, c₁ v ∈ L v) ∧
      ∃ (a' b' : C) (U' : Set (Fin n)),
        a' ≠ b' ∧ U'.Nonempty ∧ (∀ v ∈ U', c₂ v = a' ∨ c₂ v = b') ∧
        (G.induce U').Connected ∧
        (∀ u ∈ U', ∀ v : Fin n, G.Adj u v → (c₂ v = a' ∨ c₂ v = b') → v ∈ U') ∧
        (∀ v ∈ U', c₁ v = (if c₂ v = a' then b' else a')) ∧
        (∀ v ∉ U', c₁ v = c₂ v) := by
  refine ⟨hL₂, hL₁, a, b, U, hab, hU_ne, ?_, hU_conn, ?_, ?_, ?_⟩
  · intro v hv
    rcases hU_colors v hv with h1 | h1
    · rw [hc₂_in v hv, if_pos h1]; exact Or.inr rfl
    · rw [hc₂_in v hv, if_neg (fun hc => hab (hc.symm.trans h1))]
      exact Or.inl rfl
  · intro u hu v hadj hv
    by_contra hvu
    rw [hc₂_out v hvu] at hv
    exact hvu (hU_closed u hu v hadj hv)
  · intro v hv
    by_cases h1 : c₁ v = a
    · have : c₂ v = b := by rw [hc₂_in v hv, if_pos h1]
      rw [this, if_neg (fun hba => hab hba.symm), h1]
    · have h2 : c₁ v = b := by
        rcases hU_colors v hv with h | h
        · exact absurd h h1
        · exact h
      have : c₂ v = a := by rw [hc₂_in v hv, if_neg h1]
      rw [this, if_pos rfl, h2]
  · intro v hv
    exact (hc₂_out v hv).symm
