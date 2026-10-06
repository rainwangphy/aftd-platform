import AFTD.Prelude
import AFTD.Kb.Tcs.SchwartzZippelZeroCountLe

/-!
# schwartz_zippel_union_bound_zero_set

Topic: randomness   Node: 11fb01e9e8ad

Provenance: original. Related work: Schwartz 1980 / Zippel 1979 together with the union bound; the simultaneous form of the identity test as in Motwani & Raghavan, Randomized Algorithms, ch. 7. Concepts anchored by Mathlib `MvPolynomial.schwartz_zippel_totalDegree` and the knowledge-base node `schwartz_zippel_exists_nonzero_eval`.

Let F be an integral domain, S a nonempty finite subset of F, n a positive integer, and let k ≥ 0, d ∈ ℕ and p_1, …, p_k be nonzero polynomials in n variables over F whose total degrees are all at most d. Then the number of points x of S^n at which at least one of p_1, …, p_k vanishes is at most k·d·|S|^(n−1). In particular, if k·d < |S| then some point of S^n is nonzero for all of p_1, …, p_k simultaneously.
-/

open scoped Finset in
/-- Schwartz–Zippel with the union bound: at most k·d·|S|^(n−1) points of S^n are zeros of one of k nonzero polynomials of total degree at most d. -/
theorem schwartz_zippel_union_bound_zero_set {F : Type*} [CommRing F] [IsDomain F] [DecidableEq F]
    {n k d : ℕ} (hn : 0 < n) {S : Finset F} (hS : 0 < S.card)
    {p : Fin k → MvPolynomial (Fin n) F} (hp : ∀ i, p i ≠ 0)
    (hd : ∀ i, (p i).totalDegree ≤ d) :
    #{x ∈ Fintype.piFinset (fun _ : Fin n => S) | ∃ i, MvPolynomial.eval x (p i) = 0}
      ≤ k * (d * S.card ^ (n - 1)) := by
  let Sn := Fintype.piFinset (fun _ : Fin n => S)
  have h_sub : {x ∈ Sn | ∃ i, MvPolynomial.eval x (p i) = 0} ⊆
      Finset.univ.biUnion (fun i : Fin k => {x ∈ Sn | MvPolynomial.eval x (p i) = 0}) := by
    intro x hx
    simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and] at hx ⊢
    rcases hx with ⟨hxs, i, hpi⟩
    exact ⟨i, hxs, hpi⟩
  have h1 : #{x ∈ Sn | ∃ i, MvPolynomial.eval x (p i) = 0} ≤
      #(Finset.univ.biUnion (fun i : Fin k => {x ∈ Sn | MvPolynomial.eval x (p i) = 0})) :=
    Finset.card_le_card h_sub
  have h2 : #(Finset.univ.biUnion (fun i : Fin k => {x ∈ Sn | MvPolynomial.eval x (p i) = 0})) ≤
      k * (d * S.card ^ (n - 1)) := by
    have h_bound : ∀ i ∈ (Finset.univ : Finset (Fin k)),
        #{x ∈ Sn | MvPolynomial.eval x (p i) = 0} ≤ d * S.card ^ (n - 1) := by
      intro i _
      have h_sz := schwartz_zippel_zero_count_le hn (hp i) hS
      have h_deg : (p i).totalDegree * S.card ^ (n - 1) ≤ d * S.card ^ (n - 1) :=
        Nat.mul_le_mul_right _ (hd i)
      exact le_trans h_sz h_deg
    have h_mul := Finset.card_biUnion_le_card_mul (Finset.univ : Finset (Fin k))
      (fun i => {x ∈ Sn | MvPolynomial.eval x (p i) = 0}) (d * S.card ^ (n - 1)) h_bound
    rw [Finset.card_fin] at h_mul
    exact h_mul
  exact le_trans h1 h2
