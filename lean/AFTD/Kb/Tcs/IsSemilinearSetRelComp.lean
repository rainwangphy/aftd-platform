import AFTD.Prelude

/-!
# isSemilinearSet_rel_comp

Topic: automata   Node: acea8d144a77

Provenance: helper lemma. step towards op_359_symmetric_two_counter_reachability_semilinear

For any two semilinear binary relations s₁, s₂ on ℕ × ℕ, their relational composition { p | ∃ m, (p.1, m) ∈ s₁ ∧ (m, p.2) ∈ s₂ } is a semilinear set.
-/

/-- The relational composition of two semilinear binary relations on ℕ × ℕ is semilinear. -/
theorem isSemilinearSet_rel_comp {s₁ s₂ : Set ((ℕ × ℕ) × (ℕ × ℕ))} (h₁ : IsSemilinearSet s₁) (h₂ : IsSemilinearSet s₂) : IsSemilinearSet { p : (ℕ × ℕ) × (ℕ × ℕ) | ∃ m : ℕ × ℕ, (p.1, m) ∈ s₁ ∧ (m, p.2) ∈ s₂ } := by
  open Set in
  let pi12 : ((ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) →+ ((ℕ × ℕ) × (ℕ × ℕ)) :=
    { toFun := fun (x, y, _) => (x, y)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let pi23 : ((ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) →+ ((ℕ × ℕ) × (ℕ × ℕ)) :=
    { toFun := fun (_, y, z) => (y, z)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  let pi13 : ((ℕ × ℕ) × (ℕ × ℕ) × (ℕ × ℕ)) →+ ((ℕ × ℕ) × (ℕ × ℕ)) :=
    { toFun := fun (x, _, z) => (x, z)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have heq : { p : (ℕ × ℕ) × (ℕ × ℕ) | ∃ m : ℕ × ℕ, (p.1, m) ∈ s₁ ∧ (m, p.2) ∈ s₂ } =
      pi13 '' (pi12 ⁻¹' s₁ ∩ pi23 ⁻¹' s₂) := by
    ext p
    simp only [mem_image, mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨m, h1, h2⟩
      exact ⟨(p.1, m, p.2), ⟨h1, h2⟩, Prod.ext rfl rfl⟩
    · rintro ⟨⟨x, y, z⟩, ⟨h1, h2⟩, rfl⟩
      exact ⟨y, h1, h2⟩
  rw [heq]
  exact ((h₁.preimage pi12).inter (h₂.preimage pi23)).image pi13
