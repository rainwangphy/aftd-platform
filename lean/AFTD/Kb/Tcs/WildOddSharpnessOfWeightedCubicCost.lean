import AFTD.Prelude
import AFTD.Kb.Tcs.FiniteAvoidanceOfWeightedCubicCost
import AFTD.Kb.Tcs.WildNumberCompleteOddEqIffOptimalPartition
import AFTD.Kb.Tcs.WildNumberCompleteGraphMinProperColoringGe
import AFTD.Kb.Tcs.SimpleGraphWildNumber

/-!
# wild_odd_sharpness_of_weighted_cubic_cost

Topic: graphs   Node: 293332e82579

Provenance: helper lemma. IN-342 resumed helper for OP-306, arXiv:2610.22142 Sections3.3.2 and6. This is a weighted interface to the existing finite/adaptive cubic avoidance route. The new proposed square-polynomial weighting of invalid-color counts is tested only in experiments8807,8812,8822,8824. No uniform inequality, novel wild-number bound, or research advance is asserted by this conditional helper.

At any positive odd complete-graph order n>=3, for any minimum proper coloring and any finite family of rooted floor(n/3)-block partitions with block sizes at least three, let d count colors failing to cross some proper nonempty block cut. If nonnegative real weights give a strictly negative sum of w*(d-1)*(d-3)*(d-4), the wild number equals the conjectured formula. The strict weighted inequality is a hypothesis, not a proved universal estimate.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 2000000

theorem wild_odd_sharpness_of_weighted_cubic_cost
    {J : Type*} [Fintype J] {n k : ℕ} (hn : 3≤n) (hodd : n%2=1)
    (hk : (⊤ : SimpleGraph (Fin n)).lineGraph.chromaticNumber=k)
    (c : (⊤ : SimpleGraph (Fin n)).lineGraph.Coloring (Fin k))
    (p : J → Fin n → Fin (n/3)) (root : J → Fin (n/3) → Fin n)
    (hroot : ∀ j t,p j (root j t)=t)
    (hmin : ∀ j t,3≤(univ.filter fun v => p j v=t).card)
    (w : J → ℝ) (hw : ∀ j,0≤w j)
    (h : let D : J → Finset (Fin k) := fun j => univ.filter fun i =>
        ∃ S : Finset (Fin (n/3)),S.Nonempty ∧ S≠univ ∧
          ∀ u v (huv : u≠v),p j u∈S → p j v∉S →
            c ⟨s(u,v),wild_kn_mem huv⟩≠i
      let d : J → ℕ := fun j => (D j).card
      (∑ j,w j*((d j : ℝ)-1)*((d j : ℝ)-3)*((d j : ℝ)-4))<0) :
    simple_graph_wild_number (⊤ : SimpleGraph (Fin n)) c=4*((n+1)/2)/3 := by
  classical
  let D : J → Finset (Fin k) := fun j => univ.filter fun i =>
    ∃ S : Finset (Fin (n/3)),S.Nonempty ∧ S≠univ ∧
      ∀ u v (huv : u≠v),p j u∈S → p j v∉S →
        c ⟨s(u,v),wild_kn_mem huv⟩≠i
  let d : J → ℕ := fun j => (D j).card
  obtain ⟨j,hj⟩ := finite_avoidance_of_weighted_cubic_cost d w hw h
  apply (wild_number_complete_odd_eq_iff_optimal_partition hn hodd hk c).mpr
  refine ⟨p j,root j,hroot j,hmin j,?_⟩
  intro e S hS hS'
  by_contra hnot
  have hno : ∀ u v (huv : u≠v),p j u∈S → p j v∉S →
      c ⟨s(u,v),wild_kn_mem huv⟩≠c e := by
    intro u v huv hu hv hc
    exact hnot ⟨u,v,huv,hu,hv,hc⟩
  have hi : c e∈D j := mem_filter.mpr ⟨mem_univ _,S,hS,hS',hno⟩
  have hpos : 0<(D j).card := card_pos.mpr ⟨c e,hi⟩
  exact (Nat.ne_of_gt hpos) hj
