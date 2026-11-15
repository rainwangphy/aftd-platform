import AFTD.Prelude
import AFTD.Kb.Tcs.Op75Tm2Pushes

/-!
# op75_tm2_step_aux_length

Topic: np_completeness   Node: 5dad290f0ff6

Provenance: helper lemma. OP-75 Karp-reduction composition: finite-statement stack-growth bound in the repository TM2 model.

Executing one TM2 statement increases any chosen stack length by at most the syntactic push bound.
-/

theorem op75_tm2_step_aux_length {K : Type} [DecidableEq K] {Γ : K → Type} {Λ σ : Type} (s : Turing.TM2.Stmt Γ Λ σ) (v : σ)
    (S : ∀ k, List (Γ k)) (j : K) :
    ((Turing.TM2.stepAux s v S).stk j).length ≤ (S j).length + op75_tm2_pushes s := by
  induction s generalizing v S with
  | push k f q ih =>
      simp only [Turing.TM2.stepAux, op75_tm2_pushes]
      have h := ih v (Function.update S k (f v :: S k))
      by_cases hj : j = k
      · subst j
        simp only [Function.update_self, List.length_cons] at h
        omega
      · simp only [Function.update_of_ne hj] at h
        omega
  | peek k f q ih =>
      simp only [Turing.TM2.stepAux, op75_tm2_pushes]
      exact ih _ _
  | pop k f q ih =>
      simp only [Turing.TM2.stepAux, op75_tm2_pushes]
      have h := ih (f v (S k).head?) (Function.update S k (S k).tail)
      by_cases hj : j = k
      · subst j
        simp only [Function.update_self] at h
        have ht : (S k).tail.length ≤ (S k).length := by simp
        omega
      · simp only [Function.update_of_ne hj] at h
        exact h
  | load f q ih =>
      simp only [Turing.TM2.stepAux, op75_tm2_pushes]
      exact ih _ _
  | branch f q r ihq ihr =>
      simp only [Turing.TM2.stepAux, op75_tm2_pushes]
      cases hb : f v with
      | false =>
          change ((Turing.TM2.stepAux r v S).stk j).length ≤ (S j).length + max (op75_tm2_pushes q) (op75_tm2_pushes r)
          have h := ihr v S
          have hm := le_max_right (op75_tm2_pushes q) (op75_tm2_pushes r)
          omega
      | true =>
          change ((Turing.TM2.stepAux q v S).stk j).length ≤ (S j).length + max (op75_tm2_pushes q) (op75_tm2_pushes r)
          have h := ihq v S
          have hm := le_max_left (op75_tm2_pushes q) (op75_tm2_pushes r)
          omega
  | goto f => simp [Turing.TM2.stepAux, op75_tm2_pushes]
  | halt => simp [Turing.TM2.stepAux, op75_tm2_pushes]
