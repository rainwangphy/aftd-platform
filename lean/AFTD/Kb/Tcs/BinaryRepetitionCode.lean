import AFTD.Prelude

/-!
# binary_repetition_code

Topic: information   Node: e8b760e04b4c

Provenance: formalization of a published result. Source: arXiv:2611.18156 Section IV-A

For an explicit natural number n, the binary repetition code `binary_repetition_code n` is the `Finset (Fin n → Fin 2)` containing the constant zero function and the constant one function: `{(fun _ => 0), (fun _ => 1)}`.
-/

/-- The binary repetition code of length n consisting of the all-zeros and all-ones words as a Finset. -/
def binary_repetition_code (n : ℕ) : Finset (Fin n → Fin 2) := {(fun _ => 0), (fun _ => 1)}
