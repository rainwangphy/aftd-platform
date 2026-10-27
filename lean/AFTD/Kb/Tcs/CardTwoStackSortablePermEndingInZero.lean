import AFTD.Prelude

/-!
# card_two_stack_sortable_perm_ending_in_zero

Topic: combinatorics   Node: 23362ebab59d

Provenance: formalization of a published result. Source: arXiv:2610.32824 Theorem 1.3

For every non-negative integer n, the number of permutations of {0, 1, ..., n} that end with 0 and are 2-stack-sortable is equal to the n-th Motzkin number.
-/

/-- The number of 2-stack-sortable permutations of {0, ..., n} ending in 0 is the n-th Motzkin number. -/
theorem card_two_stack_sortable_perm_ending_in_zero (n : ℕ) :
    let s : List (Fin (n + 1)) → List (Fin (n + 1)) := fun l =>
      let rec aux : List (Fin (n + 1)) → List (Fin (n + 1)) → List (Fin (n + 1))
        | [], stack => stack
        | x :: xs, [] => aux xs [x]
        | x :: xs, t :: stack =>
          if t < x then t :: aux (x :: xs) stack else aux xs (x :: t :: stack)
      aux l []
    let M : ℕ → ℕ := fun k =>
      let rec motz : ℕ → ℕ
        | 0 => 1
        | m + 1 => motz m + ∑ i : Fin m, motz i.val * motz (m - 1 - i.val)
      motz k
    (Finset.filter (fun (σ : Equiv.Perm (Fin (n + 1))) =>
      σ (Fin.last n) = 0 ∧ (s (s (List.ofFn σ))).Pairwise (· ≤ ·))
    Finset.univ).card = M n := by first | (simp_all; done) | omega | decide | linarith | positivity | (aesop; done)
