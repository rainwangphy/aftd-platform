import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.Ef1costArith
import AFTD.Kb.GameTheoryEconomics.Ef1costPairOk
import AFTD.Kb.GameTheoryEconomics.Ef1costStage

/-!
# ef1cost_core

Topic: fair_division   Node: 6784921955bb

Core lemma (greedy transfer by cost ratio). Agent `P` (costs `u`) holds `X`, agent `Q` (costs `v`) holds `Xᶜ`; every chore is held by an agent for whom it is weakly cheaper, and `Q` is not EF1. Moving `Q`'s chores to `P` in increasing order of `u/v` until `Q` becomes EF1 yields an EF1 split `Y ⊇ X` whose extra social cost is at most `3 - 2√2`.
-/

/-- Core lemma (greedy transfer by cost ratio). Agent `P` (costs `u`) holds `X`, agent `Q` (costs `v`) holds `Xᶜ`; every chore is held by an agent for whom it is weakly cheaper, and `Q` is not EF1. Moving `Q`'s chores to `P` in increasing order of `u/v` until `Q` becomes EF1 yields an EF1 split `Y ⊇ X` whose extra social cost is at most `3 - 2√2`. -/
lemma ef1cost_core {m : ℕ} (u v : Fin m → ℝ) (hu0 : ∀ j, 0 ≤ u j) (hv0 : ∀ j, 0 ≤ v j)
    (hu1 : ∑ j, u j = 1) (hv1 : ∑ j, v j = 1) (X : Finset (Fin m))
    (hX : ∀ j ∈ X, u j ≤ v j) (hB : ∀ j ∉ X, v j ≤ u j)
    (hQ : ¬ ef1cost_pair_ok v Xᶜ X) :
    ∃ Y : Finset (Fin m), X ⊆ Y ∧ ef1cost_pair_ok u Y Yᶜ ∧ ef1cost_pair_ok v Yᶜ Y ∧
      ∑ j ∈ Y \ X, (u j - v j) ≤ 3 - 2 * Real.sqrt 2 := by
  classical
  have h0 : (∅ : Finset (Fin m)) ∈ (Xᶜ).powerset.filter (ef1cost_stage u v X) := by
    rw [Finset.mem_filter, Finset.mem_powerset]
    refine ⟨Finset.empty_subset _, Finset.empty_subset _, ?_, ?_⟩
    · simpa using hQ
    · simp
  obtain ⟨S, hS, hSmax⟩ :=
    Finset.exists_max_image ((Xᶜ).powerset.filter (ef1cost_stage u v X)) Finset.card ⟨∅, h0⟩
  rw [Finset.mem_filter] at hS
  obtain ⟨-, hSX, hSnot, hSpair⟩ := hS
  -- the remaining chores of `Q`, and the one of minimum ratio among those `Q` values positively
  have hpos : ((Xᶜ \ S).filter (fun f => 0 < v f)).Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty, Finset.filter_eq_empty_iff] at hne
    apply hSnot
    left
    have : ∑ j ∈ Xᶜ \ S, v j = 0 :=
      Finset.sum_eq_zero (fun j hj => le_antisymm (not_lt.mp (hne hj)) (hv0 j))
    rw [this]
    exact Finset.sum_nonneg (fun j _ => hv0 j)
  obtain ⟨e, he, hemin⟩ :=
    Finset.exists_min_image ((Xᶜ \ S).filter (fun f => 0 < v f)) (fun f => u f / v f) hpos
  rw [Finset.mem_filter] at he
  obtain ⟨heR0, hve⟩ := he
  have heX : e ∉ X := Finset.mem_compl.mp (Finset.mem_sdiff.mp heR0).1
  have heS : e ∉ S := (Finset.mem_sdiff.mp heR0).2
  have hall : ∀ f ∈ Xᶜ \ S, u e * v f ≤ u f * v e := by
    intro f hf
    rcases (hv0 f).lt_or_eq with hvf | hvf
    · have := hemin f (Finset.mem_filter.mpr ⟨hf, hvf⟩)
      rwa [div_le_div_iff₀ hve hvf] at this
    · rw [← hvf, mul_zero]
      exact mul_nonneg (hu0 f) hve.le
  have hsub : insert e S ⊆ Xᶜ := Finset.insert_subset (Finset.mem_compl.mpr heX) hSX
  have hYc : (X ∪ insert e S)ᶜ = (Xᶜ \ S).erase e := by
    ext j
    simp only [Finset.mem_compl, Finset.mem_union, Finset.mem_insert, Finset.mem_erase,
      Finset.mem_sdiff]
    tauto
  have hsd : Xᶜ \ insert e S = (Xᶜ \ S).erase e := by
    ext j
    simp only [Finset.mem_compl, Finset.mem_insert, Finset.mem_erase, Finset.mem_sdiff]
    tauto
  -- `Q` is EF1 after moving `e` (maximality of `S`)
  have hQY : ef1cost_pair_ok v (X ∪ insert e S)ᶜ (X ∪ insert e S) := by
    by_contra hnot
    have hstage : insert e S ∈ (Xᶜ).powerset.filter (ef1cost_stage u v X) := by
      rw [Finset.mem_filter, Finset.mem_powerset]
      refine ⟨hsub, hsub, ?_, ?_⟩
      · rwa [hsd, ← hYc]
      · intro e' he' f hf
        rw [hsd] at hf
        have hf0 : f ∈ Xᶜ \ S := Finset.mem_of_mem_erase hf
        rcases Finset.mem_insert.mp he' with rfl | he'
        · exact hall f hf0
        · exact hSpair e' he' f hf0
    have := hSmax _ hstage
    rw [Finset.card_insert_of_notMem heS] at this
    omega
  -- bookkeeping of sums
  have hdisj : Disjoint X (insert e S) :=
    Finset.disjoint_left.mpr (fun j hjX hj => Finset.mem_compl.mp (hsub hj) hjX)
  have hdisjS : Disjoint X S :=
    Finset.disjoint_left.mpr (fun j hjX hj => Finset.mem_compl.mp (hSX hj) hjX)
  have hsplit : ∀ w : Fin m → ℝ,
      ∑ j, w j = ∑ j ∈ X, w j + ∑ j ∈ S, w j + w e + ∑ j ∈ (Xᶜ \ S).erase e, w j := by
    intro w
    rw [← Finset.sum_add_sum_compl X w, ← Finset.sum_sdiff hSX,
      ← Finset.add_sum_erase _ _ heR0]
    ring
  have hY : ∀ w : Fin m → ℝ,
      ∑ j ∈ X ∪ insert e S, w j = ∑ j ∈ X, w j + (w e + ∑ j ∈ S, w j) := by
    intro w
    rw [Finset.sum_union hdisj, Finset.sum_insert heS]
  have hR0 : ∀ w : Fin m → ℝ, ∑ j ∈ Xᶜ \ S, w j = w e + ∑ j ∈ (Xᶜ \ S).erase e, w j := by
    intro w
    rw [Finset.add_sum_erase _ _ heR0]
  -- the facts F4, F5, F6
  have hF4 : (∑ j ∈ S, u j) * v e ≤ u e * ∑ j ∈ S, v j := by
    rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_le_sum (fun j hj => hSpair j hj e heR0)
  have hF5 : u e * ∑ j ∈ (Xᶜ \ S).erase e, v j ≤ (∑ j ∈ (Xᶜ \ S).erase e, u j) * v e := by
    rw [Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_le_sum (fun j hj => hall j (Finset.mem_of_mem_erase hj))
  have hF6 : ∑ j ∈ X, v j + ∑ j ∈ S, v j < ∑ j ∈ (Xᶜ \ S).erase e, v j := by
    have hn : ¬ (∑ j ∈ Xᶜ \ S, v j - v e ≤ ∑ j ∈ X ∪ S, v j) :=
      fun h => hSnot (Or.inr ⟨e, heR0, h⟩)
    rw [hR0 v, Finset.sum_union hdisjS] at hn
    linarith
  have hxa : ∑ j ∈ X, u j ≤ ∑ j ∈ X, v j := Finset.sum_le_sum hX
  obtain ⟨hP, hcost⟩ := ef1cost_arith (∑ j ∈ X, v j) (∑ j ∈ S, v j) (v e)
    (∑ j ∈ (Xᶜ \ S).erase e, v j) (∑ j ∈ X, u j) (∑ j ∈ S, u j) (u e)
    (∑ j ∈ (Xᶜ \ S).erase e, u j)
    (by rw [← hsplit v]; exact hv1) (by have := hsplit u; linarith)
    (Finset.sum_nonneg (fun j _ => hu0 j)) hxa (Finset.sum_nonneg (fun j _ => hv0 j))
    (Finset.sum_nonneg (fun j _ => hv0 j)) hve (hB e heX) hF4 hF5 hF6
  refine ⟨X ∪ insert e S, Finset.subset_union_left, ?_, hQY, ?_⟩
  · right
    refine ⟨e, Finset.mem_union_right _ (Finset.mem_insert_self _ _), ?_⟩
    rw [hY u, hYc]
    linarith
  · have hXY : X ⊆ X ∪ insert e S := Finset.subset_union_left
    have k := Finset.sum_sdiff hXY (f := fun j => u j - v j)
    simp only [Finset.sum_sub_distrib] at k ⊢
    rw [hY u, hY v] at k
    linarith
