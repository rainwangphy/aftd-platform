import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MmsExistsMonotone
import AFTD.Kb.GameTheoryEconomics.MaximinShare
import AFTD.Kb.GameTheoryEconomics.BundleOf

/-!
# mms_exists_monotone_of_le

Topic: fair_division   Node: 489d6041be19

Provenance: formalization of a published result. Source: arXiv:2610.06125 (On MMS allocations with few items), Sec. 1 (remark that μ(n) ≥ n); proof via a pigeonhole argument on the MMS partition rather than the paper's one-line remark

With n ≥ 1 agents and at most n goods, monotone valuations always admit an MMS allocation (give good j to agent j); so μ(n) ≥ n.
-/

theorem mms_exists_monotone_of_le (n m : ℕ) (hn : 1 ≤ n) (hmn : m ≤ n) :
    mms_exists_monotone n m := by
  intro v hv
  refine ⟨Fin.castLE hmn, fun i => ?_⟩
  have : Nonempty (Fin m → Fin n) := ⟨fun _ => ⟨0, hn⟩⟩
  have : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  unfold maximin_share
  refine ciSup_le fun P => ?_
  have hk : ∃ k, bundle_of P k ⊆ bundle_of (Fin.castLE hmn) i := by
    by_contra hno
    push Not at hno
    have hsurj : Function.Surjective P := by
      intro k
      by_contra hk
      push Not at hk
      apply hno k
      intro x hx
      simp only [bundle_of, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      exact absurd hx (hk x)
    have hcard := Fintype.card_le_of_surjective P hsurj
    simp only [Fintype.card_fin] at hcard
    have hinj : Function.Injective P :=
      ((Fintype.bijective_iff_surjective_and_card P).2 ⟨hsurj, by simp; omega⟩).1
    apply hno (P ⟨i, by omega⟩)
    intro x hx
    simp only [bundle_of, Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
    have := hinj hx
    subst this
    ext; simp
  obtain ⟨k, hk⟩ := hk
  exact (ciInf_le (Set.finite_range _).bddBelow k).trans ((hv i).1.2 _ _ hk)
