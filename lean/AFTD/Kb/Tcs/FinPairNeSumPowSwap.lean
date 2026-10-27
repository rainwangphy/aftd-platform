import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphTChromaticPrincipalSpecialization

/-!
# fin_pair_ne_sum_pow_swap

Topic: graphs   Node: e8924b98ca43

Provenance: helper lemma. arXiv:2610.31785 (Principal specializations of the t-chromatic symmetric function), Proposition 3.16(3), symmetry used to order the part sizes

For natural numbers n, a, b, the sum over ordered pairs (j1, j2) of distinct elements of Fin n of X^(a j1 + b j2) in ℕ[X] equals the sum of X^(b j1 + a j2).
-/

theorem fin_pair_ne_sum_pow_swap (n a b : ℕ) :
    ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 ≠ p.2),
        (Polynomial.X : Polynomial ℕ) ^ (a * (p.1 : ℕ) + b * (p.2 : ℕ)) =
    ∑ p ∈ Finset.univ.filter (fun p : Fin n × Fin n => p.1 ≠ p.2),
        (Polynomial.X : Polynomial ℕ) ^ (b * (p.1 : ℕ) + a * (p.2 : ℕ)) := by
  refine Finset.sum_bij' (fun p _ => p.swap) (fun p _ => p.swap) ?_ ?_ ?_ ?_ ?_
  · intro p hp; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢; exact fun e => hp e.symm
  · intro p hp; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢; exact fun e => hp e.symm
  · intro p _; rfl
  · intro p _; rfl
  · intro p _; simp only [Prod.fst_swap, Prod.snd_swap]; ring_nf
