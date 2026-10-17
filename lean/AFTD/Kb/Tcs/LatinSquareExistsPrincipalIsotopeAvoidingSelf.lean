import AFTD.Prelude
import AFTD.Kb.Tcs.LatinSquareIs

/-!
# latin_square_exists_principal_isotope_avoiding_self

Topic: combinatorics   Node: 20f60b4a6ff5

Provenance: formalization of a published result. Source: arXiv:2610.20008 (Avoiding a partial Latin square with an isotope of a given Latin square), remark after Conjecture 4 (the conjecture is trivially true when L' = L, by a cyclic permutation of the rows).

The case L' = L: every Latin square of order n > 1 is avoided by one of its own principal isotopes (shift the rows cyclically).
-/

theorem latin_square_exists_principal_isotope_avoiding_self (n : ℕ) (hn : 1 < n)
    (L : Fin n → Fin n → Fin n) (hL : latin_square_is L) :
    ∃ π ρ : Equiv.Perm (Fin n), ∀ i j, L (π i) (ρ j) ≠ L i j := by
  refine ⟨finRotate n, 1, fun i j h => ?_⟩
  have := hL.2 j h
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [finRotate_apply] at this
  have : (1 : Fin (m + 1)) = 0 := by simpa using this
  exact absurd (congrArg Fin.val this) (by simp [Nat.mod_eq_of_lt hn])
