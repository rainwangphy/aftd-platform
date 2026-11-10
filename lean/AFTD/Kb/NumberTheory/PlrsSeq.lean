import AFTD.Prelude

/-!
# plrs_seq

Topic: elementary_number_theory   Node: e17f2edc8c09

Provenance: formalization of a published result. Source: arXiv:2611.10200, Section 1

For a list of natural numbers c : List ℕ, the standard positive linear recurrence sequence plrs_seq c : ℕ → ℤ is defined recursively by plrs_seq c 0 = 0, plrs_seq c 1 = 1, and for n : ℕ, if n + 2 ≤ c.length then plrs_seq c (n + 2) = 1 + ∑ i ∈ Finset.range (n + 1), (c.getD i 0 : ℤ) * plrs_seq c (n + 1 - i), and if n + 2 > c.length then plrs_seq c (n + 2) = ∑ i ∈ Finset.range c.length, (c.getD i 0 : ℤ) * plrs_seq c (n + 1 - i).
-/

/-- The standard positive linear recurrence sequence associated with coefficient list c. -/
def plrs_seq (c : List ℕ) : ℕ → ℤ
| 0 => 0
| 1 => 1
| n + 2 =>
  if n + 2 ≤ c.length then
    1 + ∑ i ∈ Finset.range (n + 1), (c.getD i 0 : ℤ) * plrs_seq c (n + 1 - i)
  else
    ∑ i ∈ Finset.range c.length, (c.getD i 0 : ℤ) * plrs_seq c (n + 1 - i)
