import AFTD.Prelude
import AFTD.Kb.Tcs.Op75Tm2MachineOneStepBound
import AFTD.Kb.Tcs.Op75Tm2IterMeasureBound
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# op75_tm2_output_linear_bound

Topic: np_completeness   Node: 5ec046553dc4

Provenance: helper lemma. OP-75 Karp-reduction composition: finite-statement stack-growth bound in the repository TM2 model.

For any finite TM2, there is a constant C such that for every input and output, a halting run of at most n steps has output length at most the input length plus C times n.
-/

theorem op75_tm2_output_linear_bound (tm : Turing.FinTM2) :
    ∃ C : ℕ, ∀ (i : List (tm.Γ tm.k₀)) (o : List (tm.Γ tm.k₁)) (n : ℕ),
      Nonempty (Turing.TM2OutputsInTime tm i (some o) n) → o.length ≤ i.length + C*n := by
  classical
  obtain ⟨C, hstep⟩ := op75_tm2_machine_one_step_bound tm tm.k₁
  refine ⟨C, ?_⟩
  intro i o n hh
  obtain ⟨h⟩ := hh
  have hiter : (fun x : Option tm.Cfg => x.bind tm.step)^[h.steps]
      (some (Turing.initList tm i)) = some (Turing.haltList tm o) := h.evals_in_steps
  have hb := op75_tm2_iter_measure_bound tm.step (fun c : tm.Cfg => (c.stk tm.k₁).length)
    C hstep h.steps (Turing.initList tm i) (Turing.haltList tm o) hiter
  have hout : ((Turing.haltList tm o).stk tm.k₁).length = o.length := by
    simp [Turing.haltList]
  have hin : ((Turing.initList tm i).stk tm.k₁).length ≤ i.length := by
    by_cases he : tm.k₁ = tm.k₀
    · have helper : ∀ k : tm.K, k = tm.k₀ → ((Turing.initList tm i).stk k).length = i.length := by
        intro k hk
        subst k
        simp [Turing.initList]
      exact le_of_eq (helper tm.k₁ he)
    · simp [Turing.initList, he]
  rw [hout] at hb
  have hs := h.steps_le_m
  nlinarith
