import AFTD.Prelude

/-!
# degree_list_kempe_single_vertex_diff

Topic: graphs   Node: 086e555167b4

Provenance: helper lemma. step towards three_connected_degree_list_kempe_quadratic_diameter

If two proper L-colorings α and β differ at exactly one vertex v₀, then β is reachable from α in a single L-valid Kempe change on the singleton component U = {v₀}.
-/

/-- Two proper L-colorings differing on a single vertex are connected by a 1-step Kempe change. -/
theorem degree_list_kempe_single_vertex_diff {n : ℕ} (G : SimpleGraph (Fin n))
    {C : Type} [Fintype C] [DecidableEq C] (L : Fin n → Finset C)
    (α β : G.Coloring C)
    (hLα : ∀ v, α v ∈ L v) (hLβ : ∀ v, β v ∈ L v)
    (v₀ : Fin n) (h_diff : ∀ v, v ≠ v₀ → α v = β v) (hne : α v₀ ≠ β v₀) :
    ∃ (seq : List (G.Coloring C)),
      seq ≠ [] ∧ seq.head? = some α ∧ seq.getLast? = some β ∧
      seq.length - 1 = 1 ∧
      seq.IsChain (fun c₁ c₂ => (∀ v, c₁ v ∈ L v) ∧ (∀ v, c₂ v ∈ L v) ∧
        ∃ (a b : C) (U : Set (Fin n)),
          a ≠ b ∧ U.Nonempty ∧ (∀ v ∈ U, c₁ v = a ∨ c₁ v = b) ∧
          (G.induce U).Connected ∧
          (∀ u ∈ U, ∀ v : Fin n, G.Adj u v → (c₁ v = a ∨ c₁ v = b) → v ∈ U) ∧
          (∀ v ∈ U, c₂ v = (if c₁ v = a then b else a)) ∧
          (∀ v ∉ U, c₂ v = c₁ v)) := by
  refine ⟨[α, β], by simp, by simp, by simp, by simp, ?_⟩
  rw [List.isChain_cons]
  refine ⟨?_, by simp⟩
  intro y hy
  simp only [List.head?_cons, Option.mem_some_iff] at hy
  subst hy
  refine ⟨hLα, hLβ, α v₀, β v₀, {v₀}, hne, Set.singleton_nonempty v₀, ?_, ?_, ?_, ?_, ?_⟩
  · intro v hv
    rw [Set.mem_singleton_iff.mp hv]
    exact Or.inl rfl
  · constructor
    · rintro ⟨u, hu⟩ ⟨v, hv⟩
      have hu' : u = v₀ := Set.mem_singleton_iff.mp hu
      have hv' : v = v₀ := Set.mem_singleton_iff.mp hv
      subst hu' hv'
      rfl
  · intro u hu v hadj hcol
    rw [Set.mem_singleton_iff.mp hu] at hadj
    have hne_v : v ≠ v₀ := hadj.ne'
    have hcol_v : α v = β v := h_diff v hne_v
    have hneq_a : α v ≠ α v₀ := α.valid hadj.symm
    have hneq_b : α v ≠ β v₀ := by
      rw [hcol_v]
      exact β.valid hadj.symm
    cases hcol with
    | inl ha => exact False.elim (hneq_a ha)
    | inr hb => exact False.elim (hneq_b hb)
  · intro v hv
    rw [Set.mem_singleton_iff.mp hv]
    simp
  · intro v hv
    have hne_v : v ≠ v₀ := mt Set.mem_singleton_iff.mp hv
    exact (h_diff v hne_v).symm
