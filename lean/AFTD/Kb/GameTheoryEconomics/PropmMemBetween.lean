import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EdgesBetween
import AFTD.Kb.GameTheoryEconomics.IncidentEdges
import AFTD.Kb.GameTheoryEconomics.IsOrientation

/-!
# propm_mem_between

Topic: fair_division   Node: 7378e321109c

Under an orientation, an edge incident to i that is held by another agent j lies in the parallel class of i and j.
-/

/-- Under an orientation, an edge at `i` held by `j ≠ i` lies in the parallel class `{i, j}`. -/
lemma propm_mem_between {m n : ℕ} (ends : Fin m → Fin n × Fin n) (σ : Fin m → Fin n)
    (hσ : is_orientation ends σ) {i j : Fin n} {e : Fin m} (he : e ∈ incident_edges ends i)
    (hj : σ e = j) (hij : i ≠ j) : e ∈ edges_between ends i j := by
  simp only [incident_edges, edges_between, Finset.mem_filter, Finset.mem_univ, true_and] at he ⊢
  have ho := hσ e
  rw [hj] at ho
  generalize ends e = p at he ho ⊢
  obtain ⟨a, b⟩ := p
  simp only [Prod.mk.injEq] at he ho ⊢
  rcases he with rfl | rfl <;> rcases ho with rfl | rfl
  · exact absurd rfl hij
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩
  · exact absurd rfl hij
