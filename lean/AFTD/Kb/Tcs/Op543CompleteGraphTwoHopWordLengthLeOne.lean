import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsHop
import AFTD.Kb.Tcs.SimpleGraphLeapGroup

/-!
# op_543_completeGraph_two_hop_word_length_le_one

Topic: graphs   Node: 702fa6432b15

Provenance: helper lemma. step towards op_543_leap_group_universal_quadratic_word_diameter

For the complete graph K₂ on 2 vertices, every element of its leap group is the product of at most 1 hop.
-/

/-- For the complete graph K₂ on 2 vertices, every element of its leap group is the product of at most 1 hop. -/
theorem op_543_completeGraph_two_hop_word_length_le_one :
    ∀ g ∈ simple_graph_leap_group (⊤ : SimpleGraph (Fin 2)),
      ∃ w : List (Equiv.Perm (Fin 2)), (∀ h ∈ w, simple_graph_is_hop ⊤ h) ∧
        w.length ≤ 1 ∧ w.prod = g := by
  intro g _
  have h_or : g = 1 ∨ g = Equiv.swap 0 1 := by
    fin_cases g <;> decide
  cases h_or with
  | inl h1 =>
    refine ⟨[], by simp, by norm_num, by simp [h1]⟩
  | inr h2 =>
    refine ⟨[g], ?_, le_rfl, by simp⟩
    intro h hh
    simp only [List.mem_singleton] at hh
    subst hh
    rw [h2]
    intro v
    fin_cases v <;> decide
