import AFTD.Prelude

/-!
# Pmms3cTree

Topic: fair_division   Node: 4709567eee21

A ternary tree with natural-number leaves, used to store one certificate per allocation of nine items to three agents (the allocation read as a path of nine branch choices).
-/

/-- A ternary trie of natural numbers, indexed by sequences in Fin 3. -/
inductive Pmms3cTree | leaf (w : ℕ)
  | node (t0 t1 t2 : Pmms3cTree)
