import AFTD.Prelude
import AFTD.Kb.Tcs.PrioritizedBorelStateTrace

/-!
# prioritized_borel_reverse_unique_state_trace

Topic: automata   Node: 5b7b1778d7e2

Provenance: helper lemma. arXiv:2611.10136, Section 5.2.4; reverse-unique state history lemma

If every transition relation has a unique source state for fixed reversed branch prefix, direction and target state, then two traces reaching the same branch and final state have identical state histories.
-/

theorem prioritized_borel_reverse_unique_state_trace {Q : Type} (init : Q)
    (R : List Bool → Q → Bool → Q → Prop)
    (hback : ∀ v q1 q2 d q', R v q1 d q' → R v q2 d q' → q1 = q2)
    {v q xs} (ht : PrioritizedBorelStateTrace init R v q xs) :
    ∀ ys, PrioritizedBorelStateTrace init R v q ys → xs = ys := by
  induction ht with
  | root =>
      intro ys hy
      cases hy
      rfl
  | @step v q xs d q' ht hr ih =>
      intro ys hy
      cases hy with
      | step ht' hr' =>
          have heq := hback v q _ d q' hr hr'
          subst_vars
          congr 1
          exact ih _ ht'
