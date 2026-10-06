import AFTD.Prelude
import AFTD.Kb.Tcs.SchwartzZippelZeroCountLe

/-!
# schwartz_zippel_repeated_trials_zero_count_le

Topic: randomness   Node: 4ed77e2aeecd

Provenance: original. Related work: Amplification by independent repetition of the random-evaluation identity test of Schwartz 1980 / Zippel 1979 (Motwani & Raghavan, Randomized Algorithms, ch. 7). Concepts anchored by Mathlib `MvPolynomial.schwartz_zippel_totalDegree`.

Let F be an integral domain, S a nonempty finite subset of F, n a positive integer, and p a nonzero polynomial in n variables over F of total degree d. Then for every t the number of t-tuples (x_1, …, x_t) of points of S^n at which p vanishes at every one of the t coordinates is at most (d·|S|^(n−1))^t; equivalently, t independent random trials of the evaluation test all fail with probability at most (d/|S|)^t.
-/

open scoped Finset in
/-- Amplification by repetition: the number of t-tuples of points of S^n that are all zeros of a nonzero polynomial of total degree d is at most (d·|S|^(n−1))^t. -/
theorem schwartz_zippel_repeated_trials_zero_count_le {F : Type*} [CommRing F] [IsDomain F]
    [DecidableEq F] {n t : ℕ} (hn : 0 < n) {p : MvPolynomial (Fin n) F} (hp : p ≠ 0)
    {S : Finset F} (hS : 0 < S.card) :
    #{X ∈ Fintype.piFinset (fun _ : Fin t => Fintype.piFinset (fun _ : Fin n => S)) |
        ∀ i, MvPolynomial.eval (X i) p = 0}
      ≤ (p.totalDegree * S.card ^ (n - 1)) ^ t := by
  have h_set :
    {X ∈ Fintype.piFinset (fun _ : Fin t => Fintype.piFinset (fun _ : Fin n => S)) |
        ∀ i, MvPolynomial.eval (X i) p = 0} =
    Fintype.piFinset (fun _ : Fin t =>
      {x ∈ Fintype.piFinset (fun _ : Fin n => S) | MvPolynomial.eval x p = 0}) := by
    ext X
    simp only [Finset.mem_filter, Fintype.mem_piFinset]
    constructor
    · rintro ⟨h1, h2⟩ i
      exact ⟨h1 i, h2 i⟩
    · intro h
      exact ⟨fun i => (h i).1, fun i => (h i).2⟩
  rw [h_set, Fintype.card_piFinset_const]
  exact Nat.pow_le_pow_left (schwartz_zippel_zero_count_le hn hp hS) t
