import AFTD.Prelude

/-!
# binary_extremizer_nfa

Topic: automata   Node: 91c33c246190

Provenance: original. Related work: arXiv:2610.08525, Stronger bounds on the degree of ambiguity of finite automata

For each n, binary_extremizer_nfa n is the NFA over alphabet Fin 2 with states Fin n, unique initial state 0, unique accepting state n - 1, both an a-transition and a b-transition between every forward pair p < q, an a-loop at 0, and a b-loop at n - 1.
-/

/-- The n-state binary NFA with initial state 0, accepting state n-1, all forward transitions on both letters, an a-loop at 0, and a b-loop at n-1. -/
def binary_extremizer_nfa (n : ℕ) : NFA (Fin 2) (Fin n) where
  step p k := {q | p.val < q.val ∨ (k.val = 0 ∧ p.val = 0 ∧ q.val = 0) ∨ (k.val = 1 ∧ p.val + 1 = n ∧ q.val = p.val)}
  start := {p | p.val = 0}
  accept := {q | q.val + 1 = n}
