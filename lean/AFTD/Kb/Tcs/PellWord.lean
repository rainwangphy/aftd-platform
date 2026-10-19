import AFTD.Prelude

/-!
# pell_word

Topic: automata   Node: f152269f7726

Provenance: helper lemma. step towards finitely_ambiguous_nfa_pell_lower_bound

The word u_n = c_1 c_2 c_2 c_3 c_3 c_4 ⋯ c_(n-2) c_(n-1), i.e. the concatenation, over 1 ≤ i ≤ n-2, of the two-letter block c_i c_(i+1), subscripts taken mod 5.
-/

/-- The word of length 2(n-2) on which A_n has 2·P(n-2) accepting runs. -/
def pell_word (n : ℕ) : List (Fin 5) := ((List.range (n - 2)).map (· + 1)).flatMap (fun i =>
    [⟨i % 5, Nat.mod_lt _ (by decide)⟩, ⟨(i + 1) % 5, Nat.mod_lt _ (by decide)⟩])
