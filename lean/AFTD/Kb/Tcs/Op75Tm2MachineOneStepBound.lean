import AFTD.Prelude
import AFTD.Kb.Tcs.Op75Tm2Pushes
import AFTD.Kb.Tcs.Op75Tm2StepAuxLength

/-!
# op75_tm2_machine_one_step_bound

Topic: np_completeness   Node: f256a574d343

Provenance: helper lemma. OP-75 Karp-reduction composition: finite-statement stack-growth bound in the repository TM2 model.

For any finite TM2 and any of its stacks, some constant bounds that stack’s length increase in every machine step.
-/

theorem op75_tm2_machine_one_step_bound (tm : Turing.FinTM2) (j : tm.K) :
    ∃ C : ℕ, ∀ c d : tm.Cfg, tm.step c = some d →
      (d.stk j).length ≤ (c.stk j).length + C := by
  classical
  letI : DecidableEq tm.K := tm.kDecidableEq
  letI : Fintype tm.Λ := tm.ΛFin
  let C := Finset.univ.sup (fun l : tm.Λ => op75_tm2_pushes (tm.m l))
  refine ⟨C, ?_⟩
  intro c d h
  rcases c with ⟨label, v, S⟩
  cases label with
  | none => simp [Turing.FinTM2.step, Turing.TM2.step] at h
  | some label =>
      change some (Turing.TM2.stepAux (tm.m label) v S) = some d at h
      have hd := Option.some.inj h
      subst d
      have hm : op75_tm2_pushes (tm.m label) ≤ C := by
        dsimp [C]
        exact Finset.le_sup (f := fun l : tm.Λ => op75_tm2_pushes (tm.m l)) (Finset.mem_univ label)
      exact le_trans (op75_tm2_step_aux_length (tm.m label) v S j) (Nat.add_le_add_left hm _)
