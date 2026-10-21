import AFTD.Prelude
import AFTD.Kb.Tcs.BoruvkaRound

/-!
# is_algorithm1_output

Topic: algorithms   Node: 5f51ec1def57

Provenance: formalization of a published result. Source: arXiv:2610.23032 Algorithm 1

A graph F on a finite type V is an output of Algorithm 1 on ordinal profile π : V → LinearOrder V if F is a tree (F.IsTree) and there exists a sequence of simple graphs of length k + 1 starting at the empty graph ⊥ and ending at F such that each step from seq(i) to seq(i+1) is a Borůvka round under π.
-/

/-- A tree F is an output of Algorithm 1 if it is reached from the empty forest by a sequence of Borůvka rounds. -/
def is_algorithm1_output {V : Type*} [Fintype V] (π : V → LinearOrder V) (F : SimpleGraph V) : Prop :=
  ∃ (k : ℕ) (seq : Fin (k + 1) → SimpleGraph V),
    seq 0 = ⊥ ∧
    seq (Fin.last k) = F ∧
    (∀ i : Fin k, boruvka_round π (seq i.castSucc) (seq i.succ)) ∧
    F.IsTree
