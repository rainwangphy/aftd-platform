import AFTD.Prelude

/-!
# restricted_cycle_perms_count

Topic: elementary_number_theory   Node: a978a52ca118

Provenance: formalization of a published result. Source: arXiv:2610.40342 Section 1.1

For a natural number n and a finite set S of natural numbers, the number of permutations σ of Fin n such that for every element x of Fin n, the size of the cycle containing x under σ is not in S.
-/

/-- The number of permutations of Fin n having no cycle lengths in the finite set S. -/
def restricted_cycle_perms_count (n : ℕ) (S : Finset ℕ) : ℕ := ((Finset.univ : Finset (Equiv.Perm (Fin n))).filter (fun σ =>
    ∀ x : Fin n, (Finset.univ.filter (fun y => σ.SameCycle x y)).card ∉ (S : Set ℕ))).card
