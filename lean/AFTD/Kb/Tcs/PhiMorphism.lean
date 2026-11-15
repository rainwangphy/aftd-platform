import AFTD.Prelude

/-!
# phi_morphism

Topic: combinatorics   Node: 2cd9a7e0c5c7

Provenance: formalization of a published result. Source: arXiv:2611.13676 Eq. (1)

For a positive integer k and a letter i in Fin k, phi_morphism k i is [0, i + 1] if i + 1 < k, and [0, i, i] if i + 1 = k.
-/

/-- The morphism phi_k mapping i to 0(i+1) for i < k - 1 and to 0(k-1)(k-1) for i = k - 1. -/
def phi_morphism (k : ℕ) (i : Fin k) : List (Fin k) :=
  have hk : 0 < k := lt_of_le_of_lt (Nat.zero_le i.val) i.isLt
  if h : i.val + 1 < k then
    [⟨0, hk⟩, ⟨i.val + 1, h⟩]
  else
    [⟨0, hk⟩, i, i]
