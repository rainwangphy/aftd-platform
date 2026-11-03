import AFTD.Prelude

/-!
# finite_family_overlap_multiplicity_identity

Topic: combinatorics   Node: b7ed32cf73b2

Provenance: helper lemma. Collision counting for the small-overlap route to OP-110.

For a finite family of finite sets, total incidences equal the covered-set size plus the sum of multiplicity minus one over covered elements.
-/

theorem finite_family_overlap_multiplicity_identity
    (α β : Type) [DecidableEq α] [DecidableEq β]
    (S : Finset α) (N : α → Finset β) :
    (∑ a ∈ S, (N a).card) = (S.biUnion N).card +
      ∑ e ∈ S.biUnion N, ((S.filter fun a => e ∈ N a).card - 1) := by
  classical
  let E := S.biUnion N
  have hcount : (∑ a ∈ S, (N a).card) =
      ∑ e ∈ E, (S.filter fun a => e ∈ N a).card := by
    calc
      (∑ a ∈ S, (N a).card) =
          ∑ a ∈ S, ∑ e ∈ E, if e ∈ N a then 1 else 0 := by
        apply Finset.sum_congr rfl
        intro a ha
        have hsub : N a ⊆ E := by
          intro e he
          exact Finset.mem_biUnion.mpr ⟨a, ha, he⟩
        rw [← Finset.sum_filter]
        have heq : E.filter (fun e => e ∈ N a) = N a := by
          ext e
          simp only [Finset.mem_filter]
          exact ⟨fun h => h.2, fun h => ⟨hsub h, h⟩⟩
        rw [heq]
        simp
      _ = ∑ e ∈ E, ∑ a ∈ S, if e ∈ N a then 1 else 0 := by
        rw [Finset.sum_comm]
      _ = ∑ e ∈ E, (S.filter fun a => e ∈ N a).card := by
        apply Finset.sum_congr rfl
        intro e he
        rw [← Finset.sum_filter]
        simp
  have hpos : ∀ e ∈ E, 1 ≤ (S.filter fun a => e ∈ N a).card := by
    intro e he
    obtain ⟨a, ha, hea⟩ := Finset.mem_biUnion.mp he
    exact Finset.card_pos.mpr ⟨a, Finset.mem_filter.mpr ⟨ha, hea⟩⟩
  rw [hcount]
  calc
    (∑ e ∈ E, (S.filter fun a => e ∈ N a).card) =
        ∑ e ∈ E, (1 + ((S.filter fun a => e ∈ N a).card - 1)) := by
      apply Finset.sum_congr rfl
      intro e he
      have := hpos e he
      omega
    _ = E.card + ∑ e ∈ E, ((S.filter fun a => e ∈ N a).card - 1) := by
      rw [Finset.sum_add_distrib]
      simp
