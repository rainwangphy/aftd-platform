import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EdgesBetween
import AFTD.Kb.GameTheoryEconomics.IncidentEdges

/-!
# propm_sum_incident

Topic: fair_division   Node: ec594064e57b

In a loopless multigraph, a sum over the edges incident to i splits into sums over the parallel classes at i.
-/

/-- In a loopless multigraph, a sum over `E_i` splits along the parallel classes at `i`. -/
lemma propm_sum_incident {m n : ℕ} (ends : Fin m → Fin n × Fin n)
    (hloop : ∀ e, (ends e).1 ≠ (ends e).2) (i : Fin n) (f : Fin m → ℝ) :
    ∑ e ∈ incident_edges ends i, f e = ∑ j, ∑ e ∈ edges_between ends i j, f e := by
  classical
  rw [← Finset.sum_fiberwise (incident_edges ends i)
    (fun e => if (ends e).1 = i then (ends e).2 else (ends e).1)]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr ?_ fun _ _ => rfl
  ext e
  simp only [Finset.mem_filter, incident_edges, edges_between, Finset.mem_univ, true_and]
  have hl := hloop e
  generalize ends e = p at hl ⊢
  obtain ⟨a, b⟩ := p
  simp only [Prod.mk.injEq] at hl ⊢
  by_cases ha : a = i
  · subst ha
    simp only [if_true, true_or, true_and]
    constructor
    · intro h; exact Or.inl h
    · rintro (h | ⟨h1, h2⟩)
      · exact h
      · exact absurd h2.symm hl
  · simp only [ha, if_false, false_or, false_and]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩
    · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩
