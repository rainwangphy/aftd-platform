import AFTD.Prelude

/-!
# motzkin_number

Topic: combinatorics   Node: 48a72efcecd2

Provenance: formalization of a published result. Source: arXiv:2610.32824 Definition 1.2

The n-th Motzkin number M_n is defined by M_0 = 1 and M_{n+1} = M_n + ∑_{i=0}^{n-1} M_i M_{n-1-i}.
-/

/-- The n-th Motzkin number defined recursively. -/
def motzkin_number : ℕ → ℕ
| 0 => 1
| n + 1 => motzkin_number n + ∑ i : Fin n, motzkin_number i.val * motzkin_number (n - 1 - i.val)
