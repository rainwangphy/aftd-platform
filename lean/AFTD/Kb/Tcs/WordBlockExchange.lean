import AFTD.Prelude

/-!
# WordBlockExchange

Topic: automata   Node: 58adb06373d0

Provenance: formalization of a published result. Source: arXiv:2610.39941, Section 4

A word block exchange consists of four words X, A, B, Y over an alphabet.
-/

/-- A four-part decomposition (X, A, B, Y) of words for a block exchange. -/
structure WordBlockExchange (α : Type*) where
  X : List α
  A : List α
  B : List α
  Y : List α
