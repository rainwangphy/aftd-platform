import AFTD.Prelude
import AFTD.Kb.Tcs.SchwartzZippelZeroCountLe

/-!
# freivalds_matrix_kernel_count_le

Topic: randomness   Node: c8dd25118508

Provenance: formalization of a published result. Source: Freivalds (1977), 'Probabilistic Machines Can Use Less Running Time', Section 2

Let F be a commutative ring that is an integral domain with decidable equality, n a positive integer, S a nonempty finite subset of F, and M a nonzero n × n matrix over F. Then the number of vectors r in the Cartesian product S^n (represented as Fintype.piFinset (fun _ : Fin n => S)) such that Matrix.mulVec M r = 0 is at most S.card ^ (n - 1).
-/

/-- The kernel of a nonzero matrix on a finite grid S^n has cardinality at most |S|^(n-1). -/
theorem freivalds_matrix_kernel_count_le {F : Type*} [CommRing F] [IsDomain F] [DecidableEq F]
    {n : ℕ} (hn : 0 < n) {S : Finset F} (hS : 0 < S.card)
    {M : Matrix (Fin n) (Fin n) F} (hM : M ≠ 0) :
    Finset.card (Finset.filter (fun r => Matrix.mulVec M r = 0) (Fintype.piFinset (fun _ : Fin n => S))) ≤ S.card ^ (n - 1) := by
  obtain ⟨i, j, hij⟩ : ∃ i j, M i j ≠ 0 := by
    contrapose! hM
    ext i j
    exact hM i j
  let proj : (Fin n → F) → ({k : Fin n // k ≠ j} → F) := fun r k => r k.val
  have hmaps : Set.MapsTo proj
      ↑(Finset.filter (fun r => Matrix.mulVec M r = 0) (Fintype.piFinset (fun _ : Fin n => S)))
      ↑(Fintype.piFinset (fun _ : {k : Fin n // k ≠ j} => S)) := by
    intro r hr
    rw [Finset.mem_coe, Finset.mem_filter] at hr
    rw [Finset.mem_coe, Fintype.mem_piFinset]
    intro k
    rw [Fintype.mem_piFinset] at hr
    exact hr.1 k.val
  have hinj : Set.InjOn proj
      ↑(Finset.filter (fun r => Matrix.mulVec M r = 0) (Fintype.piFinset (fun _ : Fin n => S))) := by
    intro r₁ hr₁ r₂ hr₂ hproj
    rw [Finset.mem_coe, Finset.mem_filter] at hr₁ hr₂
    have hr₁_zero := hr₁.2
    have hr₂_zero := hr₂.2
    have hd₁ : dotProduct (M i) r₁ = 0 := by
      have : Matrix.mulVec M r₁ i = 0 := by rw [hr₁_zero]; rfl
      exact this
    have hd₂ : dotProduct (M i) r₂ = 0 := by
      have : Matrix.mulVec M r₂ i = 0 := by rw [hr₂_zero]; rfl
      exact this
    change ∑ k, M i k * r₁ k = 0 at hd₁
    change ∑ k, M i k * r₂ k = 0 at hd₂
    rw [Fintype.sum_eq_add_sum_subtype_ne (fun k => M i k * r₁ k) j] at hd₁
    rw [Fintype.sum_eq_add_sum_subtype_ne (fun k => M i k * r₂ k) j] at hd₂
    have h_sum_eq : (∑ k : {k : Fin n // k ≠ j}, M i k * r₁ k) = (∑ k : {k : Fin n // k ≠ j}, M i k * r₂ k) := by
      congr 1
      ext k
      congr 1
      exact congr_fun hproj k
    have h_mul_eq : M i j * r₁ j = M i j * r₂ j := by
      apply add_right_cancel (b := ∑ k : {k : Fin n // k ≠ j}, M i k * r₁ k)
      rw [hd₁, h_sum_eq, hd₂]
    have hr_j : r₁ j = r₂ j := mul_left_cancel₀ hij h_mul_eq
    ext k
    by_cases hk : k = j
    · subst hk; exact hr_j
    · exact congr_fun hproj ⟨k, hk⟩
  have h_le := Finset.card_le_card_of_injOn proj hmaps hinj
  have h_target : (Fintype.piFinset (fun _ : {k : Fin n // k ≠ j} => S)).card = S.card ^ (n - 1) := by
    rw [Fintype.card_piFinset, Finset.prod_const, Finset.card_univ]
    have h : Fintype.card {k : Fin n // k ≠ j} = (Finset.filter (· ≠ j) Finset.univ).card := Fintype.card_subtype _
    rw [h, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ j)]
    simp
  rwa [h_target] at h_le
