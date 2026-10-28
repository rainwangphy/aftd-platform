import AFTD.Prelude
import AFTD.Kb.Tcs.OrderedBicliqueMinimumIncidenceIntervals
import AFTD.Kb.Tcs.OrderedBicliqueDyadicTreeIncidence

/-!
# ordered_biclique_dyadic_tree_intervals

Topic: combinatorics   Node: 6013edd2bf36

Provenance: helper lemma. Uniform full-root-gap and current-scale fullness reduction for OP-205 / RT-1 following arXiv:2610.15635. The reusable finite ordered-cover classification formalizes the deficiency-one structure described in arXiv:1103.3693 Corollary 2.5.6. Explicit full-class or middle-fullness hypotheses remain structural assumptions where used; optimal original counts have not been shown to imply them. No graph covering value or research advance is claimed.

A nonempty biclique at each cut of Fin g, separated by that cut and covering every ordered pair, has interval sides when each biclique satisfies the dyadic tree cardinality identity and dyadic forward pairs have unique owners, with m positive and g at least 2^(m-1).
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem ordered_biclique_dyadic_tree_intervals
    (g m : ℕ) (hm : 1 ≤ m) (hlo : 2^(m-1) ≤ g)
    (A B : Fin (g-1) → Finset (Fin g))
    (hA : ∀ r i, i ∈ A r → r.val < i.val)
    (hB : ∀ r i, i ∈ B r → i.val ≤ r.val)
    (hne : ∀ r, (A r ∪ B r).Nonempty)
    (hcover : ∀ i j : Fin g, i < j → ∃ r, i ∈ B r ∧ j ∈ A r)
    (htree : ∀ r, (A r).card + (B r).card = 1 +
      (range m).sum (fun j => (((A r).product (B r)).filter
        (fun p : Fin g × Fin g => p.2.val+2^j = p.1.val)).card))
    (hunique : ∀ j < m, ∀ i k : Fin g, k.val+2^j = i.val →
      ∃! r, i ∈ A r ∧ k ∈ B r) :
    (∀ r (i j k : Fin g), i ≤ j → j ≤ k → i ∈ A r → k ∈ A r → j ∈ A r) ∧
    (∀ r (i j k : Fin g), i ≤ j → j ≤ k → i ∈ B r → k ∈ B r → j ∈ B r) := by
  have hg : 0 < g := lt_of_lt_of_le (Nat.two_pow_pos _) hlo
  have hdis (r : Fin (g-1)) : Disjoint (A r) (B r) := by
    apply disjoint_left.mpr
    intro i hi hbi
    have := hA r i hi
    have := hB r i hbi
    omega
  exact ordered_biclique_minimum_incidence_intervals g m hg A B hA hB hne hcover
    (ordered_biclique_dyadic_tree_incidence g m hm hlo A B hdis htree hunique)
