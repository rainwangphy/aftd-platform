import AFTD.Prelude
import AFTD.Kb.Tcs.WildOptimalPartitionFiberExcess

/-!
# wild_complete_thirteen_partition_card_profile

Topic: graphs   Node: 177f73573178

Provenance: helper lemma. Certificate-soundness and finite averaging helpers for the OP-306 campaign on arXiv:2610.22142, Sections 3.3.1 and 3.3.2. The thirteen-vertex equivalence is a reduction, not a proof of the conjectured equality; the moment criterion supplies no unproved universal numerical hypothesis.

Every partition of thirteen vertices into four labeled blocks of size at least three has exactly one block of size four and all other blocks of size three.
-/

open scoped BigOperators Classical
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000

theorem wild_complete_thirteen_partition_card_profile (p : Fin 13 → Fin 4)
    (hmin : ∀ t, 3 ≤ ((Finset.univ : Finset (Fin 13)).filter (fun v => p v = t)).card) :
    ∃ t0 : Fin 4, ∀ t : Fin 4,
      ((Finset.univ : Finset (Fin 13)).filter (fun v => p v = t)).card = if t=t0 then 4 else 3 := by
  classical
  let d : Fin 4 → ℕ := fun t => ((Finset.univ : Finset (Fin 13)).filter fun v => p v=t).card
  have hsum : (∑ t : Fin 4, d t) = 13 := by
    have hi := Finset.card_eq_sum_card_fiberwise (f := p) (s := (Finset.univ : Finset (Fin 13)))
      (t := (Finset.univ : Finset (Fin 4))) (fun _ _ => Finset.mem_univ _)
    simpa only [Finset.card_univ,Fintype.card_fin] using hi.symm
  have hmin' : ∀ t, 3 ≤ d t := hmin
  have h := hsum
  rw [Fin.sum_univ_four] at h
  have h0 := hmin' 0
  have h1 := hmin' 1
  have h2 := hmin' 2
  have h3 := hmin' 3
  have hex : ∃ t0, d t0=4 := by
    by_contra! hno
    have hn0 := hno 0
    have hn1 := hno 1
    have hn2 := hno 2
    have hn3 := hno 3
    omega
  obtain ⟨t0,ht0⟩ := hex
  refine ⟨t0,?_⟩
  intro t
  change d t = (if t=t0 then 4 else 3)
  have hexcess : (∑ j : Fin 4, (d j-3)) = 1 :=
    (wild_optimal_partition_fiber_excess (n:=13) p hmin).1
  by_cases he : t=t0
  · rw [if_pos he,he]; exact ht0
  · rw [if_neg he]
    have hi : (d t-3)+(d t0-3) ≤ ∑ j : Fin 4, (d j-3) := by
      have hz := Finset.sum_le_sum_of_subset (s := ({t,t0} : Finset (Fin 4)))
        (t := (Finset.univ : Finset (Fin 4))) (f := fun j => d j-3) (Finset.subset_univ _)
      simpa only [Finset.sum_pair he] using hz
    rw [hexcess,ht0] at hi
    have := hmin' t
    omega
