import AFTD.Prelude

/-!
# perm_offset_avoiding_count

Topic: combinatorics   Node: 9b08f149de06

Provenance: formalization of a published result. Source: arXiv:2610.23958 (Unranking S-avoiding permutations with two forbidden offsets), Sec. 1 (S-avoiding permutations; U(n) = a_{-1,0}(n)); indices shifted to {0, ..., n-1}, which does not change the condition mod n

a_S(n): the number of S-avoiding permutations of an n-element set, i.e. permutations pi of {0, ..., n-1} with pi(i) - i - s not divisible by n for every i and every s in S. With S = {-1, 0} this is the menage number U(n).
-/

/-- a_S(n): the number of S-avoiding permutations of an n-element set, i.e. permutations pi of {0, ..., n-1} with pi(i) - i - s not divisible by n for every i and every s in S. With S = {-1, 0} this is the menage number U(n). -/
def perm_offset_avoiding_count (n : ℕ) (S : Finset ℤ) : ℕ :=
  (Finset.univ.filter (fun π : Equiv.Perm (Fin n) =>
    ∀ i : Fin n, ∀ s ∈ S, ¬ ((n : ℤ) ∣ ((π i : ℕ) : ℤ) - ((i : ℕ) : ℤ) - s))).card
