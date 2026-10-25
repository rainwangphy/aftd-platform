import AFTD.Prelude

/-!
# finite_lopsided_function_product_bound

Topic: graphs   Node: dbf1c406016f

Provenance: helper lemma. Algebraic helper for the finite negative-dependency local lemma; EJC 14 (2007) R63, DOI 10.37236/981, Lemma 3. Independent finite-function proof of the standard induction, with no external Lean code copied.

An abstract finite-set function with nonnegative values, decreasing event increments and local negative-dependency bounds satisfies the finite asymmetric local-lemma product bound.
-/

theorem finite_lopsided_function_product_bound
    {I : Type*} [Fintype I] [DecidableEq I]
    (F : Finset I → ℝ) (N : I → Finset I) (p x : I → ℝ)
    (hF : ∀ S, 0 ≤ F S)
    (hinc : ∀ i S T, S ⊆ T → i ∉ T →
      F T - F (insert i T) ≤ F S - F (insert i S))
    (hdep : ∀ i S, i ∉ S → Disjoint S (N i) →
      F S - F (insert i S) ≤ p i * F S)
    (hx0 : ∀ i, 0 ≤ x i) (hx1 : ∀ i, x i < 1)
    (hprob : ∀ i, p i ≤ x i * ∏ j ∈ N i, (1 - x j)) :
    (∏ i, (1 - x i)) * F ∅ ≤ F Finset.univ := by
  classical
  have chain : ∀ S : Finset I,
      (∀ T ⊂ S, ∀ i ∉ T, F T - F (insert i T) ≤ x i * F T) →
      ∀ V ⊆ S, (∏ i ∈ V, (1 - x i)) * F (S \ V) ≤ F S := by
    intro S hs V
    induction V using Finset.induction_on with
    | empty => intro _; simp
    | @insert i V hi ih =>
      intro hsub
      have hiS := hsub (Finset.mem_insert_self _ _)
      have hVS : V ⊆ S := (Finset.subset_insert _ _).trans hsub
      have hiT : i ∉ S \ insert i V := by simp
      have hproper : S \ insert i V ⊂ S :=
        (Finset.ssubset_iff_of_subset Finset.sdiff_subset).2 ⟨i, hiS, hiT⟩
      have heq : insert i (S \ insert i V) = S \ V := by
        ext j
        simp only [Finset.mem_insert, Finset.mem_sdiff]
        constructor
        · rintro (rfl | ⟨hjS, hjV⟩)
          · exact ⟨hiS, hi⟩
          · exact ⟨hjS, fun h => hjV (Or.inr h)⟩
        · rintro ⟨hjS, hjV⟩
          by_cases hji : j = i
          · exact Or.inl hji
          · exact Or.inr ⟨hjS, by simpa [hji] using hjV⟩
      have hstep := hs _ hproper i hiT
      rw [heq] at hstep
      have hprod : 0 ≤ ∏ j ∈ V, (1 - x j) :=
        Finset.prod_nonneg (fun j _ => by linarith [hx1 j])
      rw [Finset.prod_insert hi]
      calc (1 - x i) * (∏ j ∈ V, (1 - x j)) * F (S \ insert i V)
          = (∏ j ∈ V, (1 - x j)) * ((1 - x i) * F (S \ insert i V)) := by ring
        _ ≤ (∏ j ∈ V, (1 - x j)) * F (S \ V) :=
          mul_le_mul_of_nonneg_left (by linarith) hprod
        _ ≤ F S := ih hVS
  have cond : ∀ S : Finset I, ∀ i ∉ S,
      F S - F (insert i S) ≤ x i * F S := by
    intro S
    induction S using Finset.strongInduction with
    | H S ih =>
      intro i hi
      let K := S \ N i
      have hKS : K ⊆ S := Finset.sdiff_subset
      have hiK : i ∉ K := fun h => hi (hKS h)
      have hd : Disjoint K (N i) := by
        apply Finset.disjoint_left.mpr
        intro j hj hjN
        exact (Finset.mem_sdiff.mp hj).2 hjN
      have hsub : S \ K ⊆ N i := by
        intro j hj
        by_contra hjN
        exact (Finset.mem_sdiff.mp hj).2
          (Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hj).1, hjN⟩)
      have hprod : (∏ j ∈ N i, (1 - x j)) ≤ ∏ j ∈ S \ K, (1 - x j) :=
        Finset.prod_le_prod_of_subset_of_le_one hsub
          (fun j _ => by linarith [hx1 j]) (fun j _ _ => by linarith [hx0 j])
      have hc := chain S ih (S \ K) Finset.sdiff_subset
      rw [Finset.sdiff_sdiff_eq_self hKS] at hc
      calc F S - F (insert i S)
          ≤ F K - F (insert i K) := hinc i K S hKS hi
        _ ≤ p i * F K := hdep i K hiK hd
        _ ≤ (x i * ∏ j ∈ N i, (1 - x j)) * F K :=
          mul_le_mul_of_nonneg_right (hprob i) (hF K)
        _ ≤ (x i * ∏ j ∈ S \ K, (1 - x j)) * F K :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hprod (hx0 i)) (hF K)
        _ = x i * ((∏ j ∈ S \ K, (1 - x j)) * F K) := by ring
        _ ≤ x i * F S := mul_le_mul_of_nonneg_left hc (hx0 i)
  simpa using chain Finset.univ (fun T _ => cond T) Finset.univ (fun _ h => h)
