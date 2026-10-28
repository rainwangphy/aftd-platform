import AFTD.Prelude
import AFTD.Kb.Tcs.PetersenStripWitness
import AFTD.Kb.Tcs.PetersenStripBoundary
import AFTD.Kb.Tcs.MemPetersenStripBoundary
import AFTD.Kb.Tcs.PetersenStripVertex
import AFTD.Kb.Tcs.PetersenStrip

/-!
# petersen_strip_witness_boundary_card

Topic: graphs   Node: 1433abc1a3a4

Provenance: helper lemma. step towards petersen_strip_small_boundary_attainment

For each natural number k ≥ 8, the external boundary of petersen_strip_witness k has cardinality at most 2k + 1.
-/

/-- The external boundary of the witness set in the generalized Petersen strip has cardinality at most 2k + 1 for all k ≥ 8. -/
theorem petersen_strip_witness_boundary_card (k : ℕ) (hk : 8 ≤ k) : (petersen_strip_boundary k (petersen_strip_witness k)).card ≤ 2 * k + 1 := by
  set m : ℕ := k / 2 with hm
  set R : ℕ := (if (k % 2 == 0) = true then m else m + 1) with hR
  set U : Finset ℤ := (Finset.range R).biUnion (fun r => Finset.image (fun j => (↑(r*k+j) : ℤ)) (Finset.range m)) with hU
  set extra : ℤ := (↑R : ℤ) * ↑k + ↑m - 1 with hextra
  set V : Finset ℤ := insert extra U with hV
  set S : Finset PetersenStripVertex := Finset.image PetersenStripVertex.u U ∪ Finset.image PetersenStripVertex.v V with hSdef
  have hS : petersen_strip_witness k = S := by
    rw [hSdef]
    unfold petersen_strip_witness
    simp only [← hm, ← hR, ← hU, ← hextra, ← hV]
  rw [hS]
  have hm4 : 4 ≤ m := by rw [hm]; omega
  have hm1 : 1 ≤ m := by omega
  have hR1 : 1 ≤ R := by rw [hR]; split_ifs <;> omega
  have hRk : R + m = k := by
    have h2 : k % 2 = 0 ∨ k % 2 = 1 := Nat.mod_two_eq_zero_or_one k
    rw [hR, hm]
    rcases h2 with h2 | h2
    · have hb : (k % 2 == 0) = true := by simpa using h2
      rw [if_pos hb]; omega
    · have hb : ¬ ((k % 2 == 0) = true) := by simp [h2]
      rw [if_neg hb]; omega
  set A1 : Finset ℤ := Finset.image (fun r => (↑(r*k+m) : ℤ)) (Finset.range R) with hA1
  set A2 : Finset ℤ := Finset.image (fun r => (↑(r*k) : ℤ) - 1) (Finset.range R) with hA2
  set C1 : Finset ℤ := Finset.image (fun j => (↑R : ℤ) * ↑k + ↑j) (Finset.range (m-1)) with hC1
  set C3 : Finset ℤ := Finset.image (fun (j : ℕ) => (↑j : ℤ) - ↑k) (Finset.range m) with hC3
  set Bu : Finset ℤ := A1 ∪ A2 ∪ {extra} with hBu
  set Bv : Finset ℤ := C1 ∪ {extra + ↑k} ∪ C3 with hBv
  set B : Finset PetersenStripVertex := Finset.image PetersenStripVertex.u Bu ∪ Finset.image PetersenStripVertex.v Bv with hB
  have hUmem : ∀ i : ℤ, i ∈ U ↔ ∃ r ∈ Finset.range R, ∃ j ∈ Finset.range m, i = (↑(r*k+j) : ℤ) := by
    intro i
    rw [hU]
    simp only [Finset.mem_biUnion, Finset.mem_image]
    constructor
    · rintro ⟨r, hr, j, hj, hji⟩; exact ⟨r, hr, j, hj, hji.symm⟩
    · rintro ⟨r, hr, j, hj, hij⟩; exact ⟨r, hr, j, hj, hij.symm⟩
  have huS : ∀ i, (PetersenStripVertex.u i ∈ S) ↔ i ∈ U := by
    intro i; rw [hSdef]
    simp only [Finset.mem_union, Finset.mem_image]
    constructor
    · rintro (⟨i', hi', he⟩ | ⟨i', hi', he⟩)
      · cases he; exact hi'
      · exact absurd he (by simp)
    · intro hi; exact Or.inl ⟨i, hi, rfl⟩
  have hvS : ∀ i, (PetersenStripVertex.v i ∈ S) ↔ i ∈ V := by
    intro i; rw [hSdef]
    simp only [Finset.mem_union, Finset.mem_image]
    constructor
    · rintro (⟨i', hi', he⟩ | ⟨i', hi', he⟩)
      · exact absurd he (by simp)
      · cases he; exact hi'
    · intro hi; exact Or.inr ⟨i, hi, rfl⟩
  have hmemB_u : ∀ j : ℤ, j ∈ Bu → PetersenStripVertex.u j ∈ B := by
    intro j hj; rw [hB]; exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j, hj, rfl⟩)
  have hmemB_v : ∀ j : ℤ, j ∈ Bv → PetersenStripVertex.v j ∈ B := by
    intro j hj; rw [hB]; exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, hj, rfl⟩)
  have htoBu_A1 : ∀ x : ℤ, x ∈ A1 → x ∈ Bu := by
    intro x hx; rw [hBu]; exact Finset.mem_union_left _ (Finset.mem_union_left _ hx)
  have htoBu_A2 : ∀ x : ℤ, x ∈ A2 → x ∈ Bu := by
    intro x hx; rw [hBu]; exact Finset.mem_union_left _ (Finset.mem_union_right _ hx)
  have htoBu_e : extra ∈ Bu := by rw [hBu]; exact Finset.mem_union_right _ (Finset.mem_singleton_self _)
  have htoBv_C1 : ∀ x : ℤ, x ∈ C1 → x ∈ Bv := by
    intro x hx; rw [hBv]; exact Finset.mem_union_left _ (Finset.mem_union_left _ hx)
  have htoBv_s : extra + (↑k:ℤ) ∈ Bv := by
    rw [hBv]; exact Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_singleton_self _))
  have htoBv_C3 : ∀ x : ℤ, x ∈ C3 → x ∈ Bv := by
    intro x hx; rw [hBv]; exact Finset.mem_union_right _ hx
  have hLemA : ∀ i j : ℤ, i ∈ U → j = i + 1 → j ∉ U → j ∈ Bu := by
    intro i j hiU hji hjU
    obtain ⟨r, hr, j0, hj0, hi_eq⟩ := (hUmem i).mp hiU
    rw [Finset.mem_range] at hr hj0
    by_cases hc : j0 + 1 < m
    · exfalso
      apply hjU
      rw [hUmem]
      refine ⟨r, by rw [Finset.mem_range]; exact hr, j0+1, by rw [Finset.mem_range]; exact hc, ?_⟩
      rw [hji, hi_eq]; push_cast; ring
    · have hjm : j0 + 1 = m := by omega
      have hjeq : j = (↑(r*k+m) : ℤ) := by
        rw [hji, hi_eq]; push_cast; omega
      exact htoBu_A1 j (by rw [hA1]; exact Finset.mem_image.mpr ⟨r, by rw [Finset.mem_range]; exact hr, hjeq.symm⟩)
  have hLemB : ∀ i j : ℤ, i ∈ U → j = i - 1 → j ∉ U → j ∈ Bu := by
    intro i j hiU hji hjU
    obtain ⟨r, hr, j0, hj0, hi_eq⟩ := (hUmem i).mp hiU
    rw [Finset.mem_range] at hr hj0
    by_cases hc : j0 = 0
    · have hjeq : j = (↑(r*k) : ℤ) - 1 := by rw [hji, hi_eq, hc]; push_cast; ring
      exact htoBu_A2 j (by rw [hA2]; exact Finset.mem_image.mpr ⟨r, by rw [Finset.mem_range]; exact hr, hjeq.symm⟩)
    · have hj0pos : 1 ≤ j0 := by omega
      exfalso
      have hjU' : j ∈ U := by
        rw [hUmem]
        refine ⟨r, by rw [Finset.mem_range]; exact hr, j0-1, by rw [Finset.mem_range]; omega, ?_⟩
        rw [hji, hi_eq]
        have hcast : ((j0 - 1 : ℕ) : ℤ) = (j0 : ℤ) - 1 := by
          rw [Nat.cast_sub hj0pos]; norm_num
        push_cast
        rw [hcast]
        ring
      exact hjU hjU'
  have hLemC : ∀ i j : ℤ, i ∈ U → j = i + ↑k → j ∉ V → j ∈ Bv := by
    intro i j hiU hji hjV
    obtain ⟨r, hr, j0, hj0, hi_eq⟩ := (hUmem i).mp hiU
    rw [Finset.mem_range] at hr hj0
    by_cases hc : r + 1 < R
    · exfalso
      have hjU : j ∈ U := by
        rw [hUmem]
        refine ⟨r+1, by rw [Finset.mem_range]; exact hc, j0, by rw [Finset.mem_range]; exact hj0, ?_⟩
        rw [hji, hi_eq]; push_cast; ring
      rw [hV] at hjV
      exact hjV (Finset.mem_insert_of_mem hjU)
    · have hrR : r + 1 = R := by omega
      have hjne : j ≠ extra := by
        rw [hV] at hjV
        intro h; rw [h] at hjV; exact hjV (Finset.mem_insert_self _ _)
      have hjeq : j = (↑R : ℤ) * ↑k + ↑j0 := by
        rw [hji, hi_eq, ← hrR]; push_cast; ring
      have hj0lt : j0 < m - 1 := by
        have hne : (j0 : ℤ) ≠ (m : ℤ) - 1 := by
          intro heq
          apply hjne
          rw [hjeq, hextra, heq]; ring
        have hj0z : (j0 : ℤ) < (m : ℤ) := by exact_mod_cast hj0
        have hlt : (j0 : ℤ) < (m : ℤ) - 1 := by omega
        have : ((j0 + 1 : ℕ) : ℤ) < ((m : ℕ) : ℤ) := by push_cast; omega
        have hnat : j0 + 1 < m := by exact_mod_cast this
        omega
      exact htoBv_C1 j (by rw [hC1]; exact Finset.mem_image.mpr ⟨j0, by rw [Finset.mem_range]; exact hj0lt, hjeq.symm⟩)
  have hLemD : ∀ i j : ℤ, i ∈ U → j = i - ↑k → j ∉ V → j ∈ Bv := by
    intro i j hiU hji hjV
    obtain ⟨r, hr, j0, hj0, hi_eq⟩ := (hUmem i).mp hiU
    rw [Finset.mem_range] at hr hj0
    by_cases hc : r = 0
    · have hjeq : j = (↑j0 : ℤ) - ↑k := by rw [hji, hi_eq, hc]; push_cast; ring
      exact htoBv_C3 j (by rw [hC3]; exact Finset.mem_image.mpr ⟨j0, by rw [Finset.mem_range]; exact hj0, hjeq.symm⟩)
    · have hrpos : 1 ≤ r := by omega
      exfalso
      have hjU : j ∈ U := by
        rw [hUmem]
        refine ⟨r-1, by rw [Finset.mem_range]; omega, j0, by rw [Finset.mem_range]; exact hj0, ?_⟩
        rw [hji, hi_eq]
        have hcast : ((r - 1 : ℕ) : ℤ) = (r : ℤ) - 1 := by
          rw [Nat.cast_sub hrpos]; norm_num
        push_cast
        rw [hcast]
        ring
      rw [hV] at hjV
      exact hjV (Finset.mem_insert_of_mem hjU)
  have hExtraMinusK : extra - (↑k : ℤ) ∈ U := by
    rw [hUmem]
    refine ⟨R-1, by rw [Finset.mem_range]; omega, m-1, by rw [Finset.mem_range]; omega, ?_⟩
    rw [hextra]
    have hRsub : ((R-1:ℕ):ℤ) = (R:ℤ) - 1 := by rw [Nat.cast_sub hR1]; norm_num
    have hMsub : ((m-1:ℕ):ℤ) = (m:ℤ) - 1 := by rw [Nat.cast_sub hm1]; norm_num
    push_cast
    rw [hRsub, hMsub]
    ring
  have hsub : petersen_strip_boundary k S ⊆ B := by
    intro w hw
    have hwb := (mem_petersen_strip_boundary k S w).mp hw
    obtain ⟨hwS, u0, hu0, hadj⟩ := hwb
    cases u0 with
    | u i =>
      have hiU : i ∈ U := (huS i).mp hu0
      cases w with
      | u j =>
        have hcase : j = i + 1 ∨ j = i - 1 := by simpa only [petersen_strip] using hadj
        have hjU : j ∉ U := fun h => hwS ((huS j).mpr h)
        rcases hcase with h | h
        · exact hmemB_u j (hLemA i j hiU h hjU)
        · exact hmemB_u j (hLemB i j hiU h hjU)
      | v j =>
        have hcase : j = i := by simpa only [petersen_strip] using hadj
        exfalso
        apply hwS
        rw [hcase]
        exact (hvS i).mpr (by rw [hV]; exact Finset.mem_insert_of_mem hiU)
    | v i =>
      have hiV : i ∈ V := (hvS i).mp hu0
      cases w with
      | u j =>
        have hcase : j = i := by simpa only [petersen_strip] using hadj
        have hjU : j ∉ U := fun h => hwS ((huS j).mpr h)
        have hi : i = extra ∨ i ∈ U := by rw [hV] at hiV; simpa using hiV
        rcases hi with h | h
        · exact hmemB_u j (by rw [hcase, h]; exact htoBu_e)
        · exact absurd (by rw [hcase]; exact h) hjU
      | v j =>
        have hcase : k ≠ 0 ∧ (j = i + ↑k ∨ j = i - ↑k) := by simpa only [petersen_strip] using hadj
        have hjV : j ∉ V := fun h => hwS ((hvS j).mpr h)
        obtain ⟨_, hcases⟩ := hcase
        have hi : i = extra ∨ i ∈ U := by rw [hV] at hiV; simpa using hiV
        rcases hi with hie | hiU
        · rcases hcases with hjc | hjc
          · exact hmemB_v j (by rw [hjc, hie]; exact htoBv_s)
          · exfalso
            apply hjV
            rw [hjc, hie, hV]
            exact Finset.mem_insert_of_mem hExtraMinusK
        · rcases hcases with hjc | hjc
          · exact hmemB_v j (hLemC i j hiU hjc hjV)
          · exact hmemB_v j (hLemD i j hiU hjc hjV)
  have hA1card : A1.card ≤ R := by
    rw [hA1]
    exact Finset.card_image_le.trans (le_of_eq (Finset.card_range R))
  have hA2card : A2.card ≤ R := by
    rw [hA2]
    exact Finset.card_image_le.trans (le_of_eq (Finset.card_range R))
  have hC1card : C1.card ≤ m - 1 := by
    rw [hC1]
    exact Finset.card_image_le.trans (le_of_eq (Finset.card_range (m-1)))
  have hC3card : C3.card ≤ m := by
    rw [hC3]
    exact Finset.card_image_le.trans (le_of_eq (Finset.card_range m))
  have hBucard : Bu.card ≤ 2*R+1 := by
    rw [hBu]
    have h1 := Finset.card_union_le (A1 ∪ A2) ({(extra:ℤ)})
    have h2 := Finset.card_union_le A1 A2
    simp only [Finset.card_singleton] at h1
    omega
  have hBvcard : Bv.card ≤ 2*m := by
    rw [hBv]
    have h1 := Finset.card_union_le (C1 ∪ {(extra + (↑k:ℤ))}) C3
    have h2 := Finset.card_union_le C1 ({(extra + (↑k:ℤ))})
    simp only [Finset.card_singleton] at h2
    omega
  have hBcard : B.card ≤ 2*k+1 := by
    rw [hB]
    have h1 := Finset.card_union_le (Finset.image PetersenStripVertex.u Bu) (Finset.image PetersenStripVertex.v Bv)
    have h2 : (Finset.image PetersenStripVertex.u Bu).card ≤ Bu.card := Finset.card_image_le
    have h3 : (Finset.image PetersenStripVertex.v Bv).card ≤ Bv.card := Finset.card_image_le
    omega
  calc (petersen_strip_boundary k S).card ≤ B.card := Finset.card_le_card hsub
    _ ≤ 2*k+1 := hBcard
