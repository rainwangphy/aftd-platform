import AFTD.Prelude

/-!
# pell_nfa

Topic: automata   Node: 1d1fa8ea98b8

Provenance: helper lemma. step towards finitely_ambiguous_nfa_pell_lower_bound

For every n, the 5-letter automaton A_n of the paper's lower bound: a chain q_1,…,q_n in which, for each 1 ≤ i ≤ n-2, the letter c_i (subscripts mod 5) labels the transitions q_i→q_i, q_{i+1}→q_{i+1}, q_i→q_{i+2}, q_{i+1}→q_{i+2}, and the letter c_{i+1} labels q_{i+1}→q_{i+1}, q_{i+2}→q_{i+2}, q_i→q_{i+1}, q_i→q_{i+2}; the initial state is q_1 and the final state is q_n.
-/

/-- The n-state five-letter NFA of the lower bound: a union of overlapping three-state gadgets, state ⟨j⟩ being q_(j+1) and letter ⟨i⟩ being c_i. -/
def pell_nfa (n : ℕ) : NFA (Fin 5) (Fin n) where
  step := fun p k => {q | ∃ i : ℕ, 1 ≤ i ∧ i + 2 ≤ n ∧
    ((k.val = i % 5 ∧
        ((p.val = i - 1 ∧ (q.val = i - 1 ∨ q.val = i + 1)) ∨
         (p.val = i ∧ (q.val = i ∨ q.val = i + 1)))) ∨
     (k.val = (i + 1) % 5 ∧
        ((p.val = i ∧ q.val = i) ∨ (p.val = i + 1 ∧ q.val = i + 1) ∨
         (p.val = i - 1 ∧ (q.val = i ∨ q.val = i + 1))))) }
  start := {p | p.val = 0}
  accept := {q | q.val + 1 = n}
