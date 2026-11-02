import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutCycle71Graph
import AFTD.Kb.GameTheoryEconomics.MaxcutCycle71Coloring
import AFTD.Kb.GameTheoryEconomics.IsMaxcutStrongDeviation
import AFTD.Kb.GameTheoryEconomics.MaxcutCycle71ForceClosedCore
import AFTD.Kb.GameTheoryEconomics.MaxcutCycle71Field
import AFTD.Kb.GameTheoryEconomics.MaxcutUtility

/-!
# maxcut_cycle71_first_deviation_minimal

Topic: equilibria   Node: 54f3e1621a4a

Provenance: helper lemma. Explicit regular 71-vertex construction for the unweighted minimal-deviation cycle, supported by experiments 12443, 12444, 12450 and 12452.

The 32 core vertices have a profitable deviation from the first displayed profile to the second, and no proper subcoalition can profitably deviate from the first profile using any alternative coloring.
-/

/-- Outside a set `P` closed under the coalition, a deviator's utility counts at most the
neighbours in `P` and those whose old color differs from its new one. -/
theorem mc71_utility_le_filter {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (σ τ : V → Fin k) (S : Finset V) (hout : ∀ x, x ∉ S → τ x = σ x)
    (P : V → Prop) [DecidablePred P] (hP : ∀ x ∈ S, P x) (v : V) :
    maxcut_utility G τ v ≤
      (Finset.univ.filter fun x => G.Adj v x ∧ (P x ∨ σ x ≠ τ v)).card := by
  unfold maxcut_utility
  apply Finset.card_le_card
  intro x hx
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
  refine ⟨hx.1, ?_⟩
  by_cases hxS : x ∈ S
  · exact Or.inl (hP x hxS)
  · exact Or.inr (by rw [← hout x hxS]; exact hx.2)

theorem mc71_utility_le_filter_erase {V : Type} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (σ τ : V → Fin k) (S : Finset V) (hout : ∀ x, x ∉ S → τ x = σ x)
    (P : V → Prop) [DecidablePred P] (hP : ∀ x ∈ S, P x) (v w : V)
    (hw : G.Adj v w) (hPw : P w) (hτw : τ w = τ v) :
    maxcut_utility G τ v + 1 ≤
      (Finset.univ.filter fun x => G.Adj v x ∧ (P x ∨ σ x ≠ τ v)).card := by
  have hsub : (Finset.univ.filter fun x => G.Adj v x ∧ τ x ≠ τ v) ⊆
      (Finset.univ.filter fun x => G.Adj v x ∧ (P x ∨ σ x ≠ τ v)).erase w := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_erase] at hx ⊢
    refine ⟨?_, hx.1, ?_⟩
    · rintro rfl; exact hx.2 hτw
    · by_cases hxS : x ∈ S
      · exact Or.inl (hP x hxS)
      · exact Or.inr (by rw [← hout x hxS]; exact hx.2)
  have hmem : w ∈ (Finset.univ.filter fun x => G.Adj v x ∧ (P x ∨ σ x ≠ τ v)) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact ⟨hw, Or.inl hPw⟩
  have := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem hmem] at this
  unfold maxcut_utility
  have h1 := Finset.card_pos.mpr ⟨w, hmem⟩
  omega

/-- The finite count: a core vertex moving to a new color `c` gains at most one over its
first-profile utility, even if every core neighbour cooperates, and gains nothing unless `c`
is its second-profile color. -/
theorem mc71_count_check [inst : DecidableRel maxcut_cycle71_graph.Adj] :
    ∀ v : Fin 71, v.val < 32 → ∀ c : Fin 3, c ≠ maxcut_cycle71_coloring 0 v →
      (Finset.univ.filter fun x => maxcut_cycle71_graph.Adj v x ∧
          (x.val < 32 ∨ maxcut_cycle71_coloring 0 x ≠ c)).card ≤
        maxcut_utility maxcut_cycle71_graph (maxcut_cycle71_coloring 0) v +
          (if c = maxcut_cycle71_coloring 1 v then 1 else 0) := by
  have e : inst = (show DecidableRel maxcut_cycle71_graph.Adj by
      intro u v; unfold maxcut_cycle71_graph maxcut_cycle71_field SimpleGraph.fromRel; infer_instance) :=
    Subsingleton.elim _ _
  subst e
  unfold maxcut_utility
  decide +kernel

theorem mc71_minimal_aux (inst : DecidableRel maxcut_cycle71_graph.Adj) :
    ∀ S : Finset (Fin 71), S ⊂ (Finset.univ.filter fun v : Fin 71 => v.val < 32) →
      ¬ ∃ τ : Fin 71 → Fin 3, is_maxcut_strong_deviation maxcut_cycle71_graph
        (maxcut_cycle71_coloring 0) S τ := by
  rintro S hS ⟨τ, hne, hout, himp⟩
  have hcore : ∀ v ∈ S, v.val < 32 := by
    intro v hv
    have := hS.subset hv
    simpa using this
  have hMne : (S.filter fun v => τ v ≠ maxcut_cycle71_coloring 0 v).Nonempty := by
    by_contra hM
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hM
    have hτ : τ = maxcut_cycle71_coloring 0 := by
      funext x
      by_cases hx : x ∈ S
      · exact not_not.mp (hM hx)
      · exact hout x hx
    obtain ⟨v, hv⟩ := hne
    have := himp v hv
    rw [hτ] at this
    exact lt_irrefl _ this
  have hall := maxcut_cycle71_force_closed_core _ hMne
    (fun v hv => hcore v (Finset.mem_filter.mp hv).1) (by
      intro v hv w hw hadj hcol
      rw [Finset.mem_filter] at hv
      by_contra hwM
      have hτw : τ w = maxcut_cycle71_coloring 0 w := by
        by_cases hwS : w ∈ S
        · by_contra h; exact hwM (Finset.mem_filter.mpr ⟨hwS, h⟩)
        · exact hout w hwS
      have hlt := himp v hv.1
      have hchk := mc71_count_check v (hcore v hv.1) (τ v) hv.2
      have hP : ∀ x ∈ S, (fun x : Fin 71 => x.val < 32) x := hcore
      by_cases hc : τ v = maxcut_cycle71_coloring 1 v
      · have hb := mc71_utility_le_filter_erase maxcut_cycle71_graph
          (maxcut_cycle71_coloring 0) τ S hout (fun x : Fin 71 => x.val < 32) hP v w hadj hw
          (by rw [hτw, hcol, hc])
        rw [if_pos hc] at hchk
        have h2 : maxcut_utility maxcut_cycle71_graph τ v + 1 ≤
            maxcut_utility maxcut_cycle71_graph (maxcut_cycle71_coloring 0) v + 1 :=
          le_trans hb hchk
        omega
      · have hb := mc71_utility_le_filter maxcut_cycle71_graph
          (maxcut_cycle71_coloring 0) τ S hout (fun x : Fin 71 => x.val < 32) hP v
        rw [if_neg hc] at hchk
        have h2 : maxcut_utility maxcut_cycle71_graph τ v ≤
            maxcut_utility maxcut_cycle71_graph (maxcut_cycle71_coloring 0) v + 0 :=
          le_trans hb hchk
        omega)
  apply hS.2
  intro w hw
  have hw' : w.val < 32 := by simpa using hw
  exact (Finset.mem_filter.mp (hall w hw')).1

theorem maxcut_cycle71_first_deviation_minimal :
    @is_maxcut_strong_deviation _ _ maxcut_cycle71_graph (by intro u v; unfold maxcut_cycle71_graph maxcut_cycle71_field SimpleGraph.fromRel; infer_instance) 3
      (maxcut_cycle71_coloring 0) (Finset.univ.filter fun v : Fin 71 => v.val < 32) (maxcut_cycle71_coloring 1) ∧
    ∀ S : Finset (Fin 71), S ⊂ (Finset.univ.filter fun v : Fin 71 => v.val < 32) →
      ¬ ∃ τ : Fin 71 → Fin 3, @is_maxcut_strong_deviation _ _ maxcut_cycle71_graph (by intro u v; unfold maxcut_cycle71_graph maxcut_cycle71_field SimpleGraph.fromRel; infer_instance) 3
        (maxcut_cycle71_coloring 0) S τ := by
  refine ⟨?_, ?_⟩
  · unfold is_maxcut_strong_deviation maxcut_utility
    decide +kernel
  · exact mc71_minimal_aux _
