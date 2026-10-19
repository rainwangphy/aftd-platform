import AFTD.Prelude

/-!
# AdaptivePolicy

Topic: online_algorithms   Node: 6ebcc9376b53

Provenance: formalization of a published result. Source: arXiv:2610.13775, Sec. 2.1

A fully adaptive search policy for Pandora's problem with n boxes, represented as a decision tree that at each step either stops or opens a box and branches on its revealed value.
-/

/-- A fully adaptive search policy for Pandora's problem as a decision tree. -/
inductive AdaptivePolicy (n : ℕ) where
  | stop : AdaptivePolicy n
  | openBox (b : Fin n) (cont : ℝ → AdaptivePolicy n) : AdaptivePolicy n
