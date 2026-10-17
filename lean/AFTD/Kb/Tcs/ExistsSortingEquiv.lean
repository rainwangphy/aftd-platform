import AFTD.Prelude
import AFTD.Kb.Tcs.SingularValues
import AFTD.Kb.Tcs.SingularValuesSorted

/-!
# exists_sorting_equiv

Topic: quantum   Node: 6553c2616c91

Provenance: formalization of a published result. Source: QuantumInfo, `exists_sorting_equiv`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/Majorization.lean (Copyright (c) 2026 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

There exists a bijection `σ : Fin (card d) ≃ d` such that `singularValues M (σ i) = singularValuesSorted M i` for all `i`.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BigOperators Matrix in
variable {d : Type*} [Fintype d] [DecidableEq d] in
set_option backward.isDefEq.respectTransparency false in
/-- There exists a bijection `σ : Fin (card d) ≃ d` such that `singularValues M (σ i) = singularValuesSorted M i` for all `i`. -/
lemma exists_sorting_equiv (M : Matrix d d ℂ) :
    ∃ σ : Fin (Fintype.card d) ≃ d,
    ∀ i, singularValues M (σ i) = singularValuesSorted M i := by
  -- Apply the lemma `exists_subset_prod_eq_sorted_prod` to obtain the bijection `σ`.
  have h_bij : ∃ σ : Fin (Fintype.card d) ≃ d, ∀ i, singularValues M (σ i) = singularValuesSorted M i := by
    have h_perm : Multiset.ofList (List.ofFn (singularValuesSorted M)) = Multiset.ofList (List.ofFn (singularValues M ∘ (Fintype.equivFin d).symm)) := by
      have h_multiset : Multiset.ofList (List.ofFn (singularValues M ∘ (Fintype.equivFin d).symm)) = Finset.univ.val.map (singularValues M) := by
        have h_multiset : Finset.univ.val = Multiset.map (fun i => (Fintype.equivFin d).symm i) (Finset.univ.val) := by
          exact Eq.symm (Multiset.map_univ_val_equiv (Fintype.equivFin d |> Equiv.symm))
        rw [h_multiset, Multiset.map_map]
        aesop
      have h_multiset_sorted : Multiset.ofList (List.ofFn (singularValuesSorted M)) = Multiset.map (singularValues M) Finset.univ.val := by
        have h_multiset_sorted_eq : List.ofFn (singularValuesSorted M) = Multiset.sort (Multiset.map (singularValues M) Finset.univ.val) (· ≥ ·) := by
          refine' List.ext_get _ _ <;> simp [List.ofFn_eq_map] at *; aesop (simp_config := { singlePass := true })
        exact h_multiset_sorted_eq ▸ by simp
      rw [h_multiset, h_multiset_sorted]
    have h_perm : List.Perm (List.ofFn (singularValuesSorted M)) (List.ofFn (singularValues M ∘ (Fintype.equivFin d).symm)) := by
      exact Multiset.coe_eq_coe.mp h_perm
    have h_perm : ∃ σ : Fin (Fintype.card d) ≃ Fin (Fintype.card d), ∀ i, singularValuesSorted M i = singularValues M (Fintype.equivFin d |>.symm (σ i)) := by
      have h_perm : ∀ {l1 l2 : List ℝ}, l1.Perm l2 → ∃ σ : Fin l1.length ≃ Fin l2.length, ∀ i, l1.get i = l2.get (σ i) := by
        intros l1 l2 h_perm; induction' h_perm with l1 l2 h_perm ih <;> simp_all
        · obtain ⟨σ, hσ⟩ := ‹∃ σ : Fin l2.length ≃ Fin h_perm.length, ∀ i : Fin l2.length, l2[i] = h_perm[σ i]›; use Equiv.ofBijective (fun i => Fin.cases 0 (fun i => Fin.succ (σ i)) i) ⟨fun i j hij => ?_, fun i => ?_⟩
          simp_all [Fin.forall_fin_succ]
          · rcases i with ⟨_ | i, hi⟩ <;> rcases j with ⟨_ | j, hj⟩ <;> simp_all [Fin.ext_iff]
            simpa [Fin.ext_iff] using σ.injective (Fin.ext hij)
          · refine i.cases ?_ ?_
            · simp [Fin.exists_fin_succ]
            · simp only [Fin.exists_fin_succ, Fin.cases_zero, Fin.cases_succ, Fin.succ_inj]
              exact fun i => Or.inr ⟨σ.symm i, by simp⟩
        · refine' ⟨Equiv.swap ⟨0, by simp⟩ ⟨1, by simp⟩, _⟩; simp [Fin.forall_fin_succ]; aesop
        · rename_i h₁ h₂ h₃ h₄
          obtain ⟨σ₁, hσ₁⟩ := h₃
          obtain ⟨σ₂, hσ₂⟩ := h₄
          use σ₁.trans σ₂
          simp [hσ₁, hσ₂]
      obtain ⟨σ, hσ⟩ := h_perm ‹_›
      refine ⟨Equiv.ofBijective (fun i => ⟨σ ⟨i, ?_⟩, ?_⟩) ⟨?_, ?_⟩, ?_⟩
      · simp
      · exact lt_of_lt_of_le (Fin.is_lt _) (by simp)
      · norm_num [Function.Injective, Function.Surjective]
        exact fun i j hij => Fin.ext <| by simpa [Fin.ext_iff] using σ.injective <| Fin.ext hij
      · intro b
        obtain ⟨a, ha⟩ : ∃ a : Fin (List.ofFn (singularValuesSorted M)).length, σ a = ⟨b, by simp⟩ := by
          exact σ.surjective _
        use ⟨a, lt_of_lt_of_le a.2 (by simp)⟩
        exact Fin.ext (by simp [ha])
      · intro i
        specialize hσ ⟨i, by simp⟩
        simp_all
    exact ⟨Equiv.trans h_perm.choose (Fintype.equivFin d |> Equiv.symm), fun i => h_perm.choose_spec i ▸ rfl⟩
  exact ⟨h_bij.choose, fun i => by simpa only [Equiv.symm_apply_eq] using h_bij.choose_spec i⟩
