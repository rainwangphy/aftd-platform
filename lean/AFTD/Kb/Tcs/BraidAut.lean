import AFTD.Prelude

/-!
# braid_aut

Topic: combinatorics   Node: 995d20cb470f

Provenance: formalization of a published result. Source: arXiv:2611.15540, Section 1, p. 3

For any map R : X × X → X × X on a type X, braid_aut R is the subgroup of permutations σ of X that commute with R in the sense that (σ × σ) ∘ R = R ∘ (σ × σ).
-/

/-- The automorphism group of a set-theoretic braid map R on X as a subgroup of Equiv.Perm X. -/
def braid_aut {X : Type*} (R : X × X → X × X) : Subgroup (Equiv.Perm X) where
  carrier := {σ | Prod.map (⇑σ) (⇑σ) ∘ R = R ∘ Prod.map (⇑σ) (⇑σ)}
  mul_mem' := by
    intro a b ha hb
    change Prod.map (⇑a ∘ ⇑b) (⇑a ∘ ⇑b) ∘ R = R ∘ Prod.map (⇑a ∘ ⇑b) (⇑a ∘ ⇑b)
    have h : Prod.map (⇑a ∘ ⇑b) (⇑a ∘ ⇑b) = Prod.map (⇑a) (⇑a) ∘ Prod.map (⇑b) (⇑b) := by
      ext ⟨x, y⟩ <;> rfl
    rw [h, Function.comp_assoc, hb, ← Function.comp_assoc, ha, Function.comp_assoc]
  one_mem' := by
    ext ⟨x, y⟩ <;> rfl
  inv_mem' := by
    intro a ha
    have h_inv : Prod.map (⇑a⁻¹) (⇑a⁻¹) ∘ Prod.map (⇑a) (⇑a) = id := by
      ext ⟨x, y⟩ <;> simp
    have h_inv' : Prod.map (⇑a) (⇑a) ∘ Prod.map (⇑a⁻¹) (⇑a⁻¹) = id := by
      ext ⟨x, y⟩ <;> simp
    calc Prod.map (⇑a⁻¹) (⇑a⁻¹) ∘ R
      _ = Prod.map (⇑a⁻¹) (⇑a⁻¹) ∘ R ∘ id := by rw [Function.comp_id]
      _ = Prod.map (⇑a⁻¹) (⇑a⁻¹) ∘ R ∘ (Prod.map (⇑a) (⇑a) ∘ Prod.map (⇑a⁻¹) (⇑a⁻¹)) := by rw [h_inv']
      _ = (Prod.map (⇑a⁻¹) (⇑a⁻¹) ∘ (R ∘ Prod.map (⇑a) (⇑a))) ∘ Prod.map (⇑a⁻¹) (⇑a⁻¹) := by
        repeat rw [Function.comp_assoc]
      _ = (Prod.map (⇑a⁻¹) (⇑a⁻¹) ∘ (Prod.map (⇑a) (⇑a) ∘ R)) ∘ Prod.map (⇑a⁻¹) (⇑a⁻¹) := by rw [← ha]
      _ = ((Prod.map (⇑a⁻¹) (⇑a⁻¹) ∘ Prod.map (⇑a) (⇑a)) ∘ R) ∘ Prod.map (⇑a⁻¹) (⇑a⁻¹) := by
        rw [← Function.comp_assoc (Prod.map (⇑a⁻¹) (⇑a⁻¹))]
      _ = (id ∘ R) ∘ Prod.map (⇑a⁻¹) (⇑a⁻¹) := by rw [h_inv]
      _ = R ∘ Prod.map (⇑a⁻¹) (⇑a⁻¹) := by rw [Function.id_comp]
