import AFTD.Prelude

/-!
# degree_list_kempe_chain_trans

Topic: graphs   Node: 8c260dd8582c

Provenance: helper lemma. step towards three_connected_degree_list_kempe_quadratic_diameter

Degree-list Kempe chains are transitive under concatenation: if α can reach γ in k₁ steps and γ can reach β in k₂ steps, then α can reach β in k₁ + k₂ steps.
-/

/-- Concatenation of degree-list Kempe chains: if α reaches γ in k₁ steps and γ reaches β in k₂ steps, then α reaches β in k₁ + k₂ steps. -/
theorem degree_list_kempe_chain_trans {n : ℕ} (G : SimpleGraph (Fin n))
    {C : Type} [Fintype C] [DecidableEq C] (L : Fin n → Finset C)
    (α γ β : G.Coloring C) (k₁ k₂ : ℕ)
    (seq₁ seq₂ : List (G.Coloring C))
    (h₁_ne : seq₁ ≠ []) (h₁_head : seq₁.head? = some α) (h₁_last : seq₁.getLast? = some γ)
    (h₁_len : seq₁.length - 1 = k₁)
    (h₁_chain : seq₁.IsChain (fun c₁ c₂ => (∀ v, c₁ v ∈ L v) ∧ (∀ v, c₂ v ∈ L v) ∧
      ∃ (a b : C) (U : Set (Fin n)),
        a ≠ b ∧ U.Nonempty ∧ (∀ v ∈ U, c₁ v = a ∨ c₁ v = b) ∧
        (G.induce U).Connected ∧
        (∀ u ∈ U, ∀ v : Fin n, G.Adj u v → (c₁ v = a ∨ c₁ v = b) → v ∈ U) ∧
        (∀ v ∈ U, c₂ v = (if c₁ v = a then b else a)) ∧
        (∀ v ∉ U, c₂ v = c₁ v)))
    (h₂_ne : seq₂ ≠ []) (h₂_head : seq₂.head? = some γ) (h₂_last : seq₂.getLast? = some β)
    (h₂_len : seq₂.length - 1 = k₂)
    (h₂_chain : seq₂.IsChain (fun c₁ c₂ => (∀ v, c₁ v ∈ L v) ∧ (∀ v, c₂ v ∈ L v) ∧
      ∃ (a b : C) (U : Set (Fin n)),
        a ≠ b ∧ U.Nonempty ∧ (∀ v ∈ U, c₁ v = a ∨ c₁ v = b) ∧
        (G.induce U).Connected ∧
        (∀ u ∈ U, ∀ v : Fin n, G.Adj u v → (c₁ v = a ∨ c₁ v = b) → v ∈ U) ∧
        (∀ v ∈ U, c₂ v = (if c₁ v = a then b else a)) ∧
        (∀ v ∉ U, c₂ v = c₁ v))) :
    ∃ (seq : List (G.Coloring C)),
      seq ≠ [] ∧ seq.head? = some α ∧ seq.getLast? = some β ∧
      seq.length - 1 = k₁ + k₂ ∧
      seq.IsChain (fun c₁ c₂ => (∀ v, c₁ v ∈ L v) ∧ (∀ v, c₂ v ∈ L v) ∧
        ∃ (a b : C) (U : Set (Fin n)),
          a ≠ b ∧ U.Nonempty ∧ (∀ v ∈ U, c₁ v = a ∨ c₁ v = b) ∧
          (G.induce U).Connected ∧
          (∀ u ∈ U, ∀ v : Fin n, G.Adj u v → (c₁ v = a ∨ c₁ v = b) → v ∈ U) ∧
          (∀ v ∈ U, c₂ v = (if c₁ v = a then b else a)) ∧
          (∀ v ∉ U, c₂ v = c₁ v)) := by
  let R : G.Coloring C → G.Coloring C → Prop := fun c₁ c₂ =>
    (∀ v, c₁ v ∈ L v) ∧ (∀ v, c₂ v ∈ L v) ∧
      ∃ (a b : C) (U : Set (Fin n)),
        a ≠ b ∧ U.Nonempty ∧ (∀ v ∈ U, c₁ v = a ∨ c₁ v = b) ∧
        (G.induce U).Connected ∧
        (∀ u ∈ U, ∀ v : Fin n, G.Adj u v → (c₁ v = a ∨ c₁ v = b) → v ∈ U) ∧
        (∀ v ∈ U, c₂ v = (if c₁ v = a then b else a)) ∧
        (∀ v ∉ U, c₂ v = c₁ v)
  have h₁_chain' : List.IsChain R seq₁ := h₁_chain
  have h₂_chain' : List.IsChain R seq₂ := h₂_chain
  have h₂_chain_tail : List.IsChain R seq₂.tail := h₂_chain'.tail
  have hhead : γ ∈ seq₂.head? := by rw [h₂_head]; simp
  have hseq₂ : seq₂ = γ :: seq₂.tail := (List.cons_head?_tail hhead).symm
  refine ⟨seq₁ ++ seq₂.tail, ?_, ?_, ?_, ?_, ?_⟩
  · simp [h₁_ne]
  · simpa [List.head?_append, h₁_ne] using h₁_head
  · by_cases ht : seq₂.tail = []
    · have hseq₂' : seq₂ = [γ] := by simpa [ht] using hseq₂
      have hγβ : γ = β := by simpa [hseq₂'] using h₂_last
      subst β
      simpa [ht, h₁_last]
    · have htail_last : seq₂.tail.getLast? = some β := by
        rw [hseq₂] at h₂_last
        simpa [List.getLast?_cons_of_ne_nil ht] using h₂_last
      simp [List.getLast?_append, h₁_last, htail_last]
  · have h₁pos : 0 < seq₁.length := List.length_pos_iff.mpr h₁_ne
    have h₂pos : 0 < seq₂.length := List.length_pos_iff.mpr h₂_ne
    have h₁len' : seq₁.length = k₁ + 1 := by omega
    have h₂len' : seq₂.length = k₂ + 1 := by omega
    rw [List.length_append, List.length_tail, h₁len', h₂len']
    omega
  · apply List.IsChain.append h₁_chain' h₂_chain_tail
    intro x hx y hy
    rw [h₁_last] at hx
    simp only [Option.mem_some_iff] at hx
    subst x
    have h2' : List.IsChain R (γ :: seq₂.tail) := by
      rw [← hseq₂]
      exact h₂_chain'
    exact (List.isChain_cons.mp h2').1 y hy
