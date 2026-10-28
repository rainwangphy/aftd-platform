import AFTD.Prelude

/-!
# biclique_incidence_sum

Topic: combinatorics   Node: 5f7b2b7c1f94

Provenance: helper lemma. Uniform full-root-gap and current-scale fullness reduction for OP-205 / RT-1 following arXiv:2610.15635. The reusable finite ordered-cover classification formalizes the deficiency-one structure described in arXiv:1103.3693 Corollary 2.5.6. Explicit full-class or middle-fullness hypotheses remain structural assumptions where used; optimal original counts have not been shown to imply them. No graph covering value or research advance is claimed.

For finite disjoint-sided bicliques, total vertex incidence counted by vertices equals total side cardinality counted by bicliques.
-/

open Finset
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000

theorem biclique_incidence_sum {I R : Type*} [Fintype I] [Fintype R] [DecidableEq I]
    (A B : R → Finset I) (hdis : ∀ r, Disjoint (A r) (B r)) :
    (∑ i, (univ.filter (fun r => i ∈ A r ∪ B r)).card) =
      ∑ r, ((A r).card + (B r).card) := by
  classical
  have he : (∑ i, (univ.filter (fun r => i ∈ A r ∪ B r)).card) =
      ∑ r, (A r ∪ B r).card := by
    simp only [card_eq_sum_ones, sum_filter]
    rw [sum_comm]
    apply sum_congr rfl
    intro r hr
    rw [← sum_filter]
    simp only [filter_mem_eq_inter, univ_inter]
  rw [he]
  exact sum_congr rfl (fun r hr => card_union_of_disjoint (hdis r))
