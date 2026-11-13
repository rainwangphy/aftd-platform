import AFTD.Prelude

/-!
# cerny_dfa

Topic: automata   Node: c50b6e44d0c2

Provenance: formalization of a published result. Source: Jan Černý, "Poznámka k homogénnym experimentom s konečnými automatmi", Mat.-Fyz. Čas. SAV 14 (1964), 208-216

For an integer n > 0, the Černý automaton C_n is the deterministic finite automaton with state set {0, ..., n-1} over the binary alphabet {false, true}, where letter false acts by cyclic increment x ↦ (x + 1) mod n, and letter true fixes 0, ..., n-2 while mapping n-1 to 0.
-/

/-- The n-state Černý automaton C_n over binary alphabet Bool = {false, true}, where false cyclically increments states modulo n and true maps n-1 to 0 while fixing other states. -/
def cerny_dfa (n : ℕ) (hn : 0 < n := by omega) : DFA Bool (Fin n) where
  step := fun x b =>
    match b with
    | false => ⟨(x.val + 1) % n, Nat.mod_lt _ hn⟩
    | true  => if x.val = n - 1 then ⟨0, hn⟩ else x
  start := ⟨0, hn⟩
  accept := ∅
