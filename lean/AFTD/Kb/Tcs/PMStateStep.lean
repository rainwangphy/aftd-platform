import AFTD.Prelude
import AFTD.Kb.Tcs.PMAns
import AFTD.Kb.Tcs.PMPosetAns
import AFTD.Kb.Tcs.PmFam
import AFTD.Kb.Tcs.PMState

/-!
# PMState.step

Topic: algorithms   Node: 8170cb661423

The adversary's move on query (a, b): the answer, and the new state.
-/

/-- The adversary's move on query `(a, b)`: the answer, and the new state. -/
def PMState.step {n : ℕ} (S : PMState n) (a b : Fin n) : PMAns × PMState n :=
  if a = b then (PMAns.inc, { S with facts := (a, b, PMAns.inc) :: S.facts })
  else if S.comp a ≠ S.comp b then
    (PMAns.inc,
      { S with
        col := fun x => if S.comp x = S.comp b then
            (if S.col a = S.col b then !S.col x else S.col x) else S.col x
        comp := fun x => if S.comp x = S.comp b then S.comp a else S.comp x
        facts := (a, b, PMAns.inc) :: S.facts })
  else if S.col a ≠ S.col b then
    (PMAns.inc, { S with facts := (a, b, PMAns.inc) :: S.facts })
  else if a ∈ S.alive ∧ b ∈ S.alive then
    (if a.val < b.val then
      (PMAns.lt,
        { S with
          rk := Function.update S.rk b ((n : ℤ) + S.alive.card - 1)
          alive := S.alive.erase b
          facts := (a, b, PMAns.lt) :: S.facts })
    else
      (PMAns.gt,
        { S with
          rk := Function.update S.rk a ((n : ℤ) + S.alive.card - 1)
          alive := S.alive.erase a
          facts := (a, b, PMAns.gt) :: S.facts }))
  else
    ((pmFam S.col S.rk).ans a b,
      { S with facts := (a, b, (pmFam S.col S.rk).ans a b) :: S.facts })
