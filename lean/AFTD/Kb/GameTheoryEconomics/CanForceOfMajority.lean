import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SatisfiesMajorityCriterion
import AFTD.Kb.GameTheoryEconomics.CanForce
import AFTD.Kb.GameTheoryEconomics.VotingOptionSet
import AFTD.Kb.GameTheoryEconomics.OrderTop
import AFTD.Kb.Tcs.G

/-!
# can_force_of_majority

Topic: social_choice   Node: a43e2813782f

Provenance: helper lemma. arXiv:2611.26224 Section 5.2

Under a voting rule f satisfying the majority criterion, any strict majority coalition C (with 2 * |C| > |N|) can force any alternative x.
-/

/-- Every alternative can be made the top element of some linear order on a finite nonempty type. -/
private lemma can_force_of_majority_aux_exists_order_top (A : Type*) [Fintype A] [Nonempty A]
    (x : A) : ∃ L : LinearOrder A, order_top L = x := by
  classical
  let g : A → ℕ := fun a => if a = x then Fintype.card A else (Fintype.equivFin A a).val
  have hgx : g x = Fintype.card A := by simp [g]
  have hga : ∀ a, a ≠ x → g a = (Fintype.equivFin A a).val := by
    intro a ha; simp [g, ha]
  have hinj : Function.Injective g := by
    intro a b hab
    by_cases ha : a = x
    · subst a
      by_cases hb : b = x
      · exact hb.symm
      · rw [hgx, hga b hb] at hab
        exact absurd hab.symm (Nat.ne_of_lt (Fintype.equivFin A b).isLt)
    · by_cases hb : b = x
      · subst b
        rw [hga a ha, hgx] at hab
        exact absurd hab (Nat.ne_of_lt (Fintype.equivFin A a).isLt)
      · rw [hga a ha, hga b hb] at hab
        exact (Fintype.equivFin A).injective (Fin.ext hab)
  let L : LinearOrder A := LinearOrder.lift' g hinj
  refine ⟨L, ?_⟩
  have hle : ∀ a b : A, L.le a b ↔ g a ≤ g b := fun a b => Iff.rfl
  have hx_top : ∀ a : A, L.le a x := by
    intro a
    rw [hle, hgx]
    by_cases ha : a = x
    · simp [g, ha]
    · rw [hga a ha]; exact Nat.le_of_lt (Fintype.equivFin A a).isLt
  show (Finset.univ : Finset A).max' _ = x
  rw [Finset.max'_eq_iff]
  exact ⟨Finset.mem_univ x, fun b _ => hx_top b⟩

/-- Under a voting rule satisfying the majority criterion, any strict majority coalition can force any alternative. -/
theorem can_force_of_majority {N A : Type*} [Fintype N] [Fintype A] [Nonempty A]
    (f : (N → LinearOrder A) → A) (h_maj : satisfies_majority_criterion f)
    (C : Finset N) (hC : Fintype.card N < 2 * C.card) (x : A) :
    can_force f C x := by
  classical
  let P : N → LinearOrder A := fun i => Classical.choose (can_force_of_majority_aux_exists_order_top A x)
  have hPtop : ∀ i : N, order_top (P i) = x := fun i =>
    Classical.choose_spec (can_force_of_majority_aux_exists_order_top A x)
  have h1 : C.card ≤ Fintype.card N := Finset.card_le_card (Finset.subset_univ C)
  refine ⟨P, ?_⟩
  rw [Set.eq_singleton_iff_unique_mem]
  constructor
  · refine ⟨P, fun i _ => rfl, ?_⟩
    apply h_maj P x
    have huniv : Finset.filter (fun i => order_top (P i) = x) Finset.univ = Finset.univ := by
      ext i; simp [hPtop i]
    rw [huniv, Finset.card_univ]
    omega
  · rintro y ⟨P', hP', rfl⟩
    apply h_maj P' x
    have hsub : C ⊆ Finset.filter (fun i => order_top (P' i) = x) Finset.univ := by
      intro i hi
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [hP' i hi]
      exact hPtop i
    have hcard := Finset.card_le_card hsub
    omega
