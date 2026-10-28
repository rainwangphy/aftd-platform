import AFTD.Prelude
import AFTD.Kb.Tcs.BicliqueExactForwardPairsSum
import AFTD.Kb.Tcs.BicliqueIncidenceSum

/-!
# ordered_biclique_dyadic_tree_incidence

Topic: combinatorics   Node: f52f20a6a598

Provenance: helper lemma. Uniform full-root-gap and current-scale fullness reduction for OP-205 / RT-1 following arXiv:2610.15635. The reusable finite ordered-cover classification formalizes the deficiency-one structure described in arXiv:1103.3693 Corollary 2.5.6. Explicit full-class or middle-fullness hypotheses remain structural assumptions where used; optimal original counts have not been shown to imply them. No graph covering value or research advance is claimed.

For g at least 2^(m-1), m positive, a family of g-1 disjoint-sided bicliques whose side sizes equal one plus their dyadic pair counts and which owns each dyadic forward pair exactly once has total vertex incidence plus 2^m equal to g(m+1).
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem ordered_biclique_dyadic_tree_incidence
    (g m : ℕ) (hm : 1 ≤ m) (hlo : 2^(m-1) ≤ g)
    (A B : Fin (g-1) → Finset (Fin g))
    (hdis : ∀ r, Disjoint (A r) (B r))
    (htree : ∀ r, (A r).card + (B r).card = 1 +
      (range m).sum (fun j => (((A r).product (B r)).filter
        (fun p : Fin g × Fin g => p.2.val+2^j = p.1.val)).card))
    (hunique : ∀ j < m, ∀ i k : Fin g, k.val+2^j = i.val →
      ∃! r, i ∈ A r ∧ k ∈ B r) :
    (∑ i : Fin g, (univ.filter
      (fun r : Fin (g-1) => i ∈ A r ∪ B r)).card) + 2^m = g*(m+1) := by
  classical
  have hpow (j : ℕ) (hj : j < m) : 2^j ≤ g :=
    (Nat.pow_le_pow_right (by decide) (by omega : j ≤ m-1)).trans hlo
  have hg : 0 < g := lt_of_lt_of_le (Nat.two_pow_pos _) hlo
  have hsum (j : ℕ) (hj : j < m) :
      (∑ r, (((A r).product (B r)).filter
        (fun p : Fin g × Fin g => p.2.val+2^j = p.1.val)).card) = g-2^j :=
    biclique_exact_forward_pairs_sum g (2^j) (hpow j hj) A B (hunique j hj)
  have htotal : (∑ r, ((A r).card+(B r).card)) =
      (g-1) + (range m).sum (fun j => g-2^j) := by
    simp_rw [htree]
    rw [sum_add_distrib]
    simp only [sum_const, card_univ, Fintype.card_fin, Nat.nsmul_eq_mul, mul_one]
    congr 1
    rw [sum_comm]
    exact sum_congr rfl (fun j hj => hsum j (mem_range.mp hj))
  have hgeom : ∀ t : ℕ, (range t).sum (fun j => 2^j) + 1 = 2^t := by
    intro t
    induction t with
    | zero => norm_num
    | succ t ih => rw [sum_range_succ, pow_succ]; omega
  have hbalance : (range m).sum (fun j => g-2^j) + (range m).sum (fun j => 2^j) = m*g := by
    rw [← sum_add_distrib]
    have he := sum_congr rfl (fun j (hj : j ∈ range m) =>
      Nat.sub_add_cancel (hpow j (mem_range.mp hj)))
    simpa only [sum_const, card_range, Nat.nsmul_eq_mul] using he
  rw [biclique_incidence_sum A B hdis, htotal]
  have hge := hgeom m
  have hmul : g*(m+1) = m*g+g := by ring
  omega
