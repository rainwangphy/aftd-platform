import AFTD.Prelude
import AFTD.Kb.Tcs.FiniteAvoidanceOfAdaptiveCubicMoments
import AFTD.Kb.Tcs.WildNumberCompleteOddEqIffOptimalPartition
import AFTD.Kb.Tcs.SimpleGraphWildNumber
import AFTD.Kb.Tcs.WildNumberCompleteGraphMinProperColoringGe

/-!
# wild_odd_sharpness_of_adaptive_cubic_moments

Topic: graphs   Node: e2214233673c

Provenance: helper lemma. OP-306 / IN-338 general-route helpers for the strict prescribed-coloring conjecture in arXiv:2610.22142, Sections3.3.2 and6. Structural analysis of binary factorizations and exact finite averaging in experiments8399,8400,8402,8414. These are conditional certificate or method-diagnostic lemmas, not a new wild-number bound or research advance.

For any minimum proper coloring at odd order n>=3 and any finite family of rooted partitions into floor(n/3) blocks of size at least three, count the colors failing to cross some proper nonempty block cut. If these counts satisfy the adaptive cubic strict moment criterion for some positive integer r, the wild number equals the conjectured floor(4*ceil(n/2)/3).
-/

open Finset
open scoped BigOperators Classical
set_option maxHeartbeats 2500000

theorem wild_odd_sharpness_of_adaptive_cubic_moments
    {J : Type*} [Fintype J] {n k : ℕ} (hn : 3 ≤ n) (hodd : n % 2 = 1)
    (hk : (⊤ : SimpleGraph (Fin n)).lineGraph.chromaticNumber = k)
    (c : (⊤ : SimpleGraph (Fin n)).lineGraph.Coloring (Fin k))
    (p : J → Fin n → Fin (n / 3)) (root : J → Fin (n / 3) → Fin n)
    (hroot : ∀ j t, p j (root j t) = t)
    (hmin : ∀ j t, 3 ≤ (univ.filter fun v => p j v = t).card)
    (r : ℕ) (hr : 1 ≤ r)
    (h : let D : J → Finset (Fin k) := fun j => univ.filter fun i =>
        ∃ S : Finset (Fin (n / 3)), S.Nonempty ∧ S ≠ univ ∧
          ∀ u v (huv : u ≠ v), p j u ∈ S → p j v ∉ S →
            c ⟨s(u,v), wild_kn_mem huv⟩ ≠ i
      let d : J → ℕ := fun j => (D j).card
      (r : ℝ) * (r + 1) * (∑ j, (d j : ℝ)) +
          6 * (∑ j, ((d j).choose 3 : ℝ)) <
        (r : ℝ) * (r + 1) * Fintype.card J +
          (4 * (r : ℝ) - 2) * (∑ j, ((d j).choose 2 : ℝ))) :
    simple_graph_wild_number (⊤ : SimpleGraph (Fin n)) c = 4 * ((n + 1) / 2) / 3 := by
  classical
  let D : J → Finset (Fin k) := fun j => univ.filter fun i =>
    ∃ S : Finset (Fin (n / 3)), S.Nonempty ∧ S ≠ univ ∧
      ∀ u v (huv : u ≠ v), p j u ∈ S → p j v ∉ S →
        c ⟨s(u,v), wild_kn_mem huv⟩ ≠ i
  let d : J → ℕ := fun j => (D j).card
  obtain ⟨j, hj⟩ := finite_avoidance_of_adaptive_cubic_moments d r hr h
  apply (wild_number_complete_odd_eq_iff_optimal_partition hn hodd hk c).mpr
  refine ⟨p j, root j, hroot j, hmin j, ?_⟩
  intro e S hS hS'
  by_contra hnot
  have hno : ∀ u v (huv : u ≠ v), p j u ∈ S → p j v ∉ S →
      c ⟨s(u,v), wild_kn_mem huv⟩ ≠ c e := by
    intro u v huv hu hv hc
    exact hnot ⟨u, v, huv, hu, hv, hc⟩
  have hi : c e ∈ D j := mem_filter.mpr ⟨mem_univ _, S, hS, hS', hno⟩
  have hpos : 0 < (D j).card := card_pos.mpr ⟨c e, hi⟩
  exact (Nat.ne_of_gt hpos) hj
