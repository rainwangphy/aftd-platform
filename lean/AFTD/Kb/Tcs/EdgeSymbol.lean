import AFTD.Prelude

/-!
# EdgeSymbol

Topic: approximation   Node: 7df13229a149

Provenance: formalization of a published result. Source: arXiv:2611.15074 Reduction 1

The three distinct edge-specific symbols c, lambda, and rho associated with each edge in the reduction.
-/

/-- Three auxiliary edge symbols used in the reduction from vertex cover to word factorization. -/
inductive EdgeSymbol
  | c
  | lambda
  | rho
  deriving DecidableEq
