import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MmsExistsMonotone
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.MaximinShare

/-!
# mms_exists_monotone_of_partition_cover

Topic: fair_division   Node: d9e5c06f7a3a

Provenance: formalization of a published result. Source: arXiv:2610.06125 (On MMS allocations with few items), Sec. 1 (an MMS allocation is one in which each agent gets a superset of a part of her MMS partition)

Reduction to MMS partitions: if for every choice of one partition P_i of the m goods into n bundles per agent there is an allocation in which every agent i receives a superset of some bundle of P_i, then MMS allocations exist for n agents and m goods with monotone valuations.
-/

theorem mms_exists_monotone_of_partition_cover (n m : ℕ) (hn : 1 ≤ n)
    (h : ∀ P : Fin n → Fin m → Fin n, ∃ σ : Fin m → Fin n, ∀ i, ∃ k,
      bundle_of (P i) k ⊆ bundle_of σ i) : mms_exists_monotone n m := by
  intro v hv
  have : Nonempty (Fin m → Fin n) := ⟨fun _ => ⟨0, hn⟩⟩
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hP : ∀ i, ∃ P : Fin m → Fin n, maximin_share (v i) n = ⨅ k, v i (bundle_of P k) := by
    intro i
    obtain ⟨P, hP⟩ := exists_eq_ciSup_of_finite
      (f := fun P : Fin m → Fin n => ⨅ k, v i (bundle_of P k))
    exact ⟨P, hP.symm⟩
  choose P hP using hP
  obtain ⟨σ, hσ⟩ := h P
  refine ⟨σ, fun i => ?_⟩
  obtain ⟨k, hk⟩ := hσ i
  rw [hP i]
  exact (ciInf_le (Set.finite_range _).bddBelow k).trans ((hv i).1.2 _ _ hk)
