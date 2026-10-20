import AFTD.Prelude
import AFTD.Kb.Tcs.TwoCounterMachineReachRel
import AFTD.Kb.Tcs.TwoCounterMachineStep
import AFTD.Kb.Tcs.TwoCounterMachine
import AFTD.Kb.Tcs.TwoCounterInstr

/-!
# diag_two_counter_machine_reach_rel_iff

Topic: automata   Node: 0304a3722fc8

Provenance: helper lemma. step towards op_360_single_counter_update_strictly_less_expressive

The reachability relation of the diagonal machine between false and true consists exactly of pairs (u, v) with v = (u.1 + 1, u.2 + 1).
-/

abbrev diag_two_counter_machine_reach_rel_iff_M : TwoCounterMachine Bool :=
  ⟨{(false, TwoCounterInstr.update 1 1, true)}⟩

theorem diag_two_counter_machine_reach_rel_iff_step (c₁ c₂ : Bool × ℕ × ℕ) :
    two_counter_machine_step diag_two_counter_machine_reach_rel_iff_M c₁ c₂ ↔
      c₁.1 = false ∧ c₂.1 = true ∧ c₂.2.1 = c₁.2.1 + 1 ∧ c₂.2.2 = c₁.2.2 + 1 := by
  dsimp [two_counter_machine_step, diag_two_counter_machine_reach_rel_iff_M]
  constructor
  · rintro (⟨w₁, w₂, h, h1, h2⟩ | ⟨h, -⟩ | ⟨h, -⟩)
    · simp only [Finset.mem_singleton, Prod.mk.injEq, TwoCounterInstr.update.injEq] at h
      obtain ⟨h1_st, ⟨rfl, rfl⟩, h2_st⟩ := h
      refine ⟨h1_st, h2_st, ?_, ?_⟩
      · exact_mod_cast h1.symm
      · exact_mod_cast h2.symm
    · simp only [Finset.mem_singleton, Prod.mk.injEq] at h
      cases h.2.1
    · simp only [Finset.mem_singleton, Prod.mk.injEq] at h
      cases h.2.1
  · rintro ⟨h1, h2, h3, h4⟩
    left
    refine ⟨1, 1, ?_, ?_, ?_⟩
    · simp [h1, h2]
    · exact_mod_cast h3.symm
    · exact_mod_cast h4.symm

/-- The reachability relation of the diagonal machine between false and true consists exactly of pairs (u, v) with v = (u.1 + 1, u.2 + 1). -/
theorem diag_two_counter_machine_reach_rel_iff (u v : ℕ × ℕ) :
    (u, v) ∈ two_counter_machine_reach_rel (⟨{(false, TwoCounterInstr.update 1 1, true)}⟩ : TwoCounterMachine Bool) false true ↔
      v.1 = u.1 + 1 ∧ v.2 = u.2 + 1 := by
  change Relation.ReflTransGen (two_counter_machine_step diag_two_counter_machine_reach_rel_iff_M) (false, u) (true, v) ↔
    v.1 = u.1 + 1 ∧ v.2 = u.2 + 1
  constructor
  · intro h
    rw [Relation.ReflTransGen.cases_head_iff] at h
    rcases h with h_refl | ⟨c, hstep, hrest⟩
    · exfalso
      have : false = true := (Prod.ext_iff.mp h_refl).1
      cases this
    · rw [diag_two_counter_machine_reach_rel_iff_step] at hstep
      rcases hstep with ⟨-, hc_state, hu1, hu2⟩
      rw [Relation.ReflTransGen.cases_head_iff] at hrest
      rcases hrest with rfl | ⟨c', hstep', -⟩
      · rw [← hu1, ← hu2]
        exact ⟨rfl, rfl⟩
      · exfalso
        rw [diag_two_counter_machine_reach_rel_iff_step] at hstep'
        rw [hc_state] at hstep'
        cases hstep'.1
  · rintro ⟨h1, h2⟩
    apply Relation.ReflTransGen.single
    rw [diag_two_counter_machine_reach_rel_iff_step]
    exact ⟨rfl, rfl, h1, h2⟩
