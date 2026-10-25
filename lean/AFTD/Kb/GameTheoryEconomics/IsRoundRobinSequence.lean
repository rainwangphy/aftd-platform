import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.RoundRobinSequence

/-!
# is_round_robin_sequence

Topic: fair_division   Node: aa18033318ea

Provenance: formalization of a published result. Source: arXiv:2610.23686, Sec. 2

A picking sequence seq of type List (Fin n) is a Round-Robin sequence if there exists an instance of NeZero n such that seq equals round_robin_sequence n seq.length.
-/

/-- A picking sequence seq of type List (Fin n) is a Round-Robin sequence if there exists an instance of NeZero n such that seq equals round_robin_sequence n seq.length. -/
def is_round_robin_sequence (n : ℕ) (seq : List (Fin n)) : Prop :=
  ∃ (_ : NeZero n), seq = round_robin_sequence n seq.length
