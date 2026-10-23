import AFTD.Prelude

/-!
# two_way_dfa

Topic: automata   Node: f43fdf733216

Provenance: formalization of a published result. Source: arXiv:2610.18897 (A factor-two lower bound for complementing two-way deterministic finite automata), Section 2.1: the 2DFA (Q, Σ, δ, s, f), with the endmarker rows of δ split off as δL and δR so that their directions are built in

A two-way deterministic finite automaton over the alphabet σ with state set Q: a partial transition δ(q, a) ∈ Q × {left (false), right (true)} on ordinary symbols, a partial transition δL(q) ∈ Q on the left endmarker (always moving right), a partial transition δR(q) ∈ Q on the right endmarker (always moving left), an initial state s and a final state f.
-/

structure two_way_dfa (σ Q : Type*) where
  δ : Q → σ → Option (Q × Bool)
  δL : Q → Option Q
  δR : Q → Option Q
  s : Q
  f : Q
