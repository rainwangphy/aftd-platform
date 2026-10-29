import AFTD.Prelude
import AFTD.Kb.Tcs.DegreeListKempeStepSymmetric

/-!
# degree_list_kempe_chain_symm

Topic: graphs   Node: 7c2e6ae4f848

Provenance: helper lemma. step towards three_connected_degree_list_kempe_quadratic_diameter

Reversal of degree-list Kempe chains: if α can reach β in k steps, then β can reach α in k steps.
-/

/-- Reversal of degree-list Kempe chains: if α reaches β in k steps, then β reaches α in k steps. -/
theorem degree_list_kempe_chain_symm {n : ℕ} (G : SimpleGraph (Fin n))
    {C : Type} [Fintype C] [DecidableEq C] (L : Fin n → Finset C)
    (α β : G.Coloring C) (k : ℕ)
    (seq : List (G.Coloring C))
    (hne : seq ≠ []) (hhead : seq.head? = some α) (hlast : seq.getLast? = some β)
    (hlen : seq.length - 1 = k)
    (hchain : seq.IsChain (fun c₁ c₂ => (∀ v, c₁ v ∈ L v) ∧ (∀ v, c₂ v ∈ L v) ∧
      ∃ (a b : C) (U : Set (Fin n)),
        a ≠ b ∧ U.Nonempty ∧ (∀ v ∈ U, c₁ v = a ∨ c₁ v = b) ∧
        (G.induce U).Connected ∧
        (∀ u ∈ U, ∀ v : Fin n, G.Adj u v → (c₁ v = a ∨ c₁ v = b) → v ∈ U) ∧
        (∀ v ∈ U, c₂ v = (if c₁ v = a then b else a)) ∧
        (∀ v ∉ U, c₂ v = c₁ v))) :
    ∃ (seq' : List (G.Coloring C)),
      seq' ≠ [] ∧ seq'.head? = some β ∧ seq'.getLast? = some α ∧
      seq'.length - 1 = k ∧
      seq'.IsChain (fun c₁ c₂ => (∀ v, c₁ v ∈ L v) ∧ (∀ v, c₂ v ∈ L v) ∧
        ∃ (a b : C) (U : Set (Fin n)),
          a ≠ b ∧ U.Nonempty ∧ (∀ v ∈ U, c₁ v = a ∨ c₁ v = b) ∧
          (G.induce U).Connected ∧
          (∀ u ∈ U, ∀ v : Fin n, G.Adj u v → (c₁ v = a ∨ c₁ v = b) → v ∈ U) ∧
          (∀ v ∈ U, c₂ v = (if c₁ v = a then b else a)) ∧
          (∀ v ∉ U, c₂ v = c₁ v)) := by
  refine ⟨seq.reverse, ?_, ?_, ?_, ?_, ?_⟩
  · exact List.reverse_ne_nil_iff.mpr hne
  · rw [List.head?_reverse, hlast]
  · rw [List.getLast?_reverse, hhead]
  · rw [List.length_reverse, hlen]
  · rw [List.isChain_reverse]
    refine hchain.imp ?_
    intro c₁ c₂ h
    rcases h with ⟨hL₁, hL₂, a, b, U, hab, hU_ne, hU_colors, hU_conn, hU_closed, hc₂_in, hc₂_out⟩
    exact degree_list_kempe_step_symmetric G L c₁ c₂ hL₁ hL₂ a b U hab hU_ne hU_colors hU_conn hU_closed hc₂_in hc₂_out
