import AFTD.Prelude

/-!
# digraph_directed_cycle_on

Topic: graphs   Node: 3f8f903456cc

Provenance: helper lemma.

s is the vertex set of a directed cycle of D: its vertices can be listed without repetition, at least two of them, each with an arc to the next and the last with an arc back to the first (a digon counts).
-/

def digraph_directed_cycle_on {α : Type} [DecidableEq α] (D : Digraph α) (s : Finset α) : Prop :=
  ∃ l : List α, l.Nodup ∧ 2 ≤ l.length ∧ l.toFinset = s ∧ l.IsChain D.Adj ∧
    ∃ a b, l.head? = some a ∧ l.getLast? = some b ∧ D.Adj b a
