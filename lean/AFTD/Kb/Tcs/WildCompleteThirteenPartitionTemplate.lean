import AFTD.Prelude
import AFTD.Kb.Tcs.FinitePartitionPermutationOfFiberCard
import AFTD.Kb.Tcs.WildCompleteThirteenPartitionCardProfile
import AFTD.Kb.Tcs.WildCompleteThirteenOneSwapRepairObstruction

/-!
# wild_complete_thirteen_partition_template

Topic: graphs   Node: 18efd2495dbb

Provenance: helper lemma. Certificate-soundness and finite averaging helpers for the OP-306 campaign on arXiv:2610.22142, Sections 3.3.1 and 3.3.2. The thirteen-vertex equivalence is a reduction, not a proof of the conjectured equality; the moment criterion supplies no unproved universal numerical hypothesis.

For every partition p of thirteen vertices into four labeled blocks of size at least three, there are vertex and block-label permutations sigma,beta such that beta(p(sigma v)) is the canonical block owner of {0,1,2},{3,4,5},{6,7,8},{9,10,11,12}.
-/

open scoped BigOperators Classical
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000

theorem wild_complete_thirteen_partition_template (p : Fin 13 → Fin 4)
    (hmin : ∀ t, 3 ≤ ((Finset.univ : Finset (Fin 13)).filter (fun v => p v = t)).card) :
    ∃ (σ : Equiv.Perm (Fin 13)) (β : Equiv.Perm (Fin 4)),
      ∀ v, β (p (σ v)) = wsc_repair_owner v := by
  classical
  obtain ⟨t0,ht0⟩ := wild_complete_thirteen_partition_card_profile p hmin
  let β : Equiv.Perm (Fin 4) := Equiv.swap t0 3
  let p' : Fin 13 → Fin 4 := fun v => β (p v)
  have hb : ∀ t : Fin 4,
      ((Finset.univ : Finset (Fin 13)).filter (fun v => wsc_repair_owner v = t)).card =
        if t=3 then 4 else 3 := by decide +kernel
  have hcard : ∀ t : Fin 4,
      ((Finset.univ : Finset (Fin 13)).filter (fun v => p' v = t)).card =
      ((Finset.univ : Finset (Fin 13)).filter (fun v => wsc_repair_owner v = t)).card := by
    intro t
    have he : ((Finset.univ : Finset (Fin 13)).filter (fun v => p' v = t)) =
        ((Finset.univ : Finset (Fin 13)).filter (fun v => p v = β t)) := by
      ext v
      simp only [Finset.mem_filter,Finset.mem_univ,true_and,p',Equiv.apply_eq_iff_eq_symm_apply,β,Equiv.symm_swap]
    rw [he,ht0,hb]
    have h3 : β (3 : Fin 4) = t0 := Equiv.swap_apply_right _ _
    have hiff : β t = t0 ↔ t=3 := by rw [← h3,β.injective.eq_iff]
    simp only [hiff]
  obtain ⟨σ,hσ⟩ := finite_partition_permutation_of_fiber_card p' wsc_repair_owner hcard
  exact ⟨σ,β,hσ⟩
