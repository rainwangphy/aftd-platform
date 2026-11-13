import AFTD.Prelude

/-!
# cerny_swap_dfa

Topic: automata   Node: d462294f3a85

Provenance: formalization of a published result. Source: Jan Černý (1964); arXiv:2611.09136

For an integer n > 0, the letter-swapped Černý automaton C_n^swap is the deterministic finite automaton with state set {0, ..., n-1} where the transitions for false and true are exchanged relative to C_n.
-/

/-- The letter-swapped Černý automaton C_n^swap where the roles of false and true are exchanged. -/
def cerny_swap_dfa (n : ℕ) (hn : 0 < n := by omega) : DFA Bool (Fin n) where
  step := fun x b =>
    match !b with
    | false => ⟨(x.val + 1) % n, Nat.mod_lt _ hn⟩
    | true  => if x.val = n - 1 then ⟨0, hn⟩ else x
  start := ⟨0, hn⟩
  accept := ∅
