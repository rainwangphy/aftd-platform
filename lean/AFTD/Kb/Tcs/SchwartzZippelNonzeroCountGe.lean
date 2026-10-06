import AFTD.Prelude
import AFTD.Kb.Tcs.SchwartzZippelZeroCountLe

/-!
# schwartz_zippel_nonzero_count_ge

Topic: randomness   Node: e08519ad12ea

Provenance: helper lemma. Schwartz 1980; Zippel 1979, in the one-sided-error form used for the randomized identity test (Motwani & Raghavan, Randomized Algorithms, ch. 7); companion of the knowledge-base node `schwartz_zippel_exists_nonzero_eval`.

Let F be an integral domain, S a nonempty finite subset of F, n a positive integer, and p a nonzero polynomial in n variables over F of total degree d. Then the number of points of S^n at which p does not vanish is at least |S|^n − d·|S|^(n−1); equivalently, at least a fraction 1 − d/|S| of the points of S^n are nonzero for p. This is the guarantee of the random-evaluation identity test: a point where p is nonzero certifies p ≠ 0, so the test has one-sided error and rejects a nonzero p with probability at most d/|S|.
-/

open scoped Finset in
/-- At least |S|^n − d·|S|^(n−1) points of S^n are nonzero for a nonzero polynomial of total degree d. -/
theorem schwartz_zippel_nonzero_count_ge {F : Type*} [CommRing F] [IsDomain F] [DecidableEq F]
    {n : ℕ} (hn : 0 < n) {p : MvPolynomial (Fin n) F} (hp : p ≠ 0) {S : Finset F}
    (hS : 0 < S.card) :
    S.card ^ n - p.totalDegree * S.card ^ (n - 1)
      ≤ #{x ∈ Fintype.piFinset (fun _ : Fin n => S) | MvPolynomial.eval x p ≠ 0} := by
  have h_le := schwartz_zippel_zero_count_le hn hp hS
  have h_sum := Finset.card_filter_add_card_filter_not (s := Fintype.piFinset (fun _ : Fin n => S))
    (fun x => MvPolynomial.eval x p = 0)
  simp only [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h_sum
  simp only [ne_eq]
  omega
