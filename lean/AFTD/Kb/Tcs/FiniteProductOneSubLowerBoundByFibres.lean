import AFTD.Prelude

/-!
# finite_product_one_sub_lower_bound_by_fibres

Topic: graphs   Node: 299efdc9ffd4

Provenance: helper lemma. Product estimate for OP-306 permutation seal events. Assign each neighboring event one shared position or vertex; the total event weight per such resource is bounded by the explicit mass certificate.

If each factor 1-w_i belongs to one of a finite set of groups, all weights are in [0,1], and every group has total weight at most M in [0,1], the product of all factors is at least (1-M) to the number of groups.
-/

theorem finite_product_one_sub_lower_bound_by_fibres_aux
    {I : Type*} [DecidableEq I] (s : Finset I) (w : I → ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i ∧ w i ≤ 1) :
    1 - ∑ i ∈ s, w i ≤ ∏ i ∈ s, (1 - w i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.prod_insert ha]
      have hwa : 0 ≤ w a ∧ w a ≤ 1 := hw a (Finset.mem_insert_self a s)
      have hws : ∀ i ∈ s, 0 ≤ w i ∧ w i ≤ 1 := fun i hi => hw i (Finset.mem_insert_of_mem hi)
      have ih' : 1 - ∑ i ∈ s, w i ≤ ∏ i ∈ s, (1 - w i) := ih hws
      have hprod_nonneg : 0 ≤ ∏ i ∈ s, (1 - w i) :=
        Finset.prod_nonneg (fun i hi => sub_nonneg.mpr (hws i hi).2)
      have hprod_le_one : ∏ i ∈ s, (1 - w i) ≤ 1 := by
        apply Finset.prod_le_one
        · intro i hi; linarith [(hws i hi).2]
        · intro i hi; linarith [(hws i hi).1]
      nlinarith

theorem finite_product_one_sub_lower_bound_by_fibres
    {I R : Type*} [DecidableEq I] [DecidableEq R]
    (N : Finset I) (S : Finset R) (f : I → R) (w : I → ℝ) (M : ℝ)
    (hM0 : 0 ≤ M) (hM1 : M ≤ 1)
    (hw : ∀ i ∈ N, 0 ≤ w i ∧ w i ≤ 1)
    (hf : ∀ i ∈ N, f i ∈ S)
    (hmass : ∀ r ∈ S, ∑ i ∈ N.filter (fun i => f i = r), w i ≤ M) :
    (1 - M) ^ S.card ≤ ∏ i ∈ N, (1 - w i) := by
  classical
  have hM : 0 ≤ M ∧ M ≤ 1 := ⟨hM0, hM1⟩
  have hfiber : ∀ r ∈ S, 1 - M ≤ ∏ i ∈ N.filter (fun i => f i = r), (1 - w i) := by
    intro r hr
    have hsub : N.filter (fun i => f i = r) ⊆ N := Finset.filter_subset _ _
    have hw' : ∀ i ∈ N.filter (fun i => f i = r), 0 ≤ w i ∧ w i ≤ 1 :=
      fun i hi => hw i (hsub hi)
    have hsum := hmass r hr
    have hprod := finite_product_one_sub_lower_bound_by_fibres_aux
      (N.filter (fun i => f i = r)) w hw'
    linarith
  calc
    (1 - M) ^ S.card = ∏ r ∈ S, (1 - M) := by rw [Finset.prod_const]
    _ ≤ ∏ r ∈ S, ∏ i ∈ N.filter (fun i => f i = r), (1 - w i) := by
      apply Finset.prod_le_prod
      · intro r hr
        linarith [hM.2]
      · intro r hr
        exact hfiber r hr
    _ = ∏ i ∈ N, (1 - w i) := by
      exact Finset.prod_fiberwise_of_maps_to hf (fun i => 1 - w i)
