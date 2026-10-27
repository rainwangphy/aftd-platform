import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphLeapGroup
import AFTD.Kb.Tcs.SimpleGraphIsHop

/-!
# op_543_completeGraph_three_hop_word_length_le_one

Topic: graphs   Node: 288c72e4ef56

Provenance: formalization of a published result. Source: arXiv:2610.18463, Proposition 2.2

For the complete graph K₃ on 3 vertices, every element of its leap group is the product of at most 1 hop.
-/

instance op_543_decidable_is_hop {V : Type*} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (h : Equiv.Perm V) :
    Decidable (simple_graph_is_hop G h) := by
  unfold simple_graph_is_hop
  infer_instance

/-- For the complete graph K_3 on 3 vertices, every element of its leap group is a product of at most 1 hop. -/
theorem op_543_completeGraph_three_hop_word_length_le_one :
    ∀ g ∈ simple_graph_leap_group (⊤ : SimpleGraph (Fin 3)),
      ∃ w : List (Equiv.Perm (Fin 3)), (∀ h ∈ w, simple_graph_is_hop ⊤ h) ∧
        w.length ≤ 1 ∧ w.prod = g := by
  have Hmul : ∀ x y : Equiv.Perm (Fin 3),
      (x = 1 ∨ simple_graph_is_hop ⊤ x) → (y = 1 ∨ simple_graph_is_hop ⊤ y) →
      (x * y = 1 ∨ simple_graph_is_hop ⊤ (x * y)) := by decide
  have Hinv : ∀ x : Equiv.Perm (Fin 3),
      (x = 1 ∨ simple_graph_is_hop ⊤ x) →
      (x⁻¹ = 1 ∨ simple_graph_is_hop ⊤ (x⁻¹)) := by decide
  intro g hg
  have h_cases : g = 1 ∨ simple_graph_is_hop ⊤ g := by
    refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hg
    · intro x hx; exact Or.inr hx
    · exact Or.inl rfl
    · intro x y _ _ hx hy; exact Hmul x y hx hy
    · intro x _ hx; exact Hinv x hx
  rcases h_cases with rfl | hg_hop
  · exact ⟨[], by simp, by simp, by simp⟩
  · exact ⟨[g], by simp [hg_hop], by simp, by simp⟩
