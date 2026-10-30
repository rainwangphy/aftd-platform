import AFTD.Prelude
import AFTD.Kb.Tcs.CyclicCubicFamily

/-!
# cyclic_cubic_family_card

Topic: quantum   Node: aed32df3c232

Provenance: helper lemma. step towards cyclic_cubic_t_count_upper_bound

For any n ≥ 6, the cardinality of cyclic_cubic_family n is 2 * n + 5.
-/

/-- The six-element alphabet `0, 1, m+2, m+3, m+4, m+5` indexing the boundary sets
of `cyclic_cubic_family (m+6)`; used to identify the boundary group with a fixed
family of ten subsets of `Fin 6`. -/
def cyclic_cubic_family_card_e6 (m : ℕ) : Fin 6 → ℕ
  | ⟨0, _⟩ => 0
  | ⟨1, _⟩ => 1
  | ⟨2, _⟩ => m + 2
  | ⟨3, _⟩ => m + 3
  | ⟨4, _⟩ => m + 4
  | _ => m + 5

/-- The explicit parametric parity family on n qubits has cardinality 2 * n + 5 for all n ≥ 6. -/
theorem cyclic_cubic_family_card (n : ℕ) (hn : 6 ≤ n) : (cyclic_cubic_family n).card = 2 * n + 5 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 6 := ⟨n - 6, by omega⟩
  let T : Finset ℕ → Finset (Fin (m + 6)) := fun s => {i | (i : ℕ) ∈ s}
  let A : Finset (Finset ℕ) := {{1}, {0,1}, {m+3}, {0,m+4}, {m+3,m+4}, {1,m+5}, {0,1,m+5}, {m+2,m+5}, {m+2,m+3,m+5}, {0,m+4,m+5}}
  let B : Finset (Finset ℕ) := (Finset.Iic (m+1)).biUnion fun k => ({insert k (Finset.Ico (k+3) (m+6)), insert k (insert (k+1) (Finset.Ico (k+3) (m+6)))} : Finset (Finset ℕ))
  let C : Finset (Finset ℕ) := ({Finset.Ico 2 (m+6), insert 0 (Finset.Ico 2 (m+6)), Finset.Iio (m+6)} : Finset (Finset ℕ))
  have hfam : cyclic_cubic_family (m+6) = (A ∪ B ∪ C).image T := rfl
  have hinj_e : Function.Injective (cyclic_cubic_family_card_e6 m) := by
    intro a b h
    fin_cases a <;> fin_cases b <;> simp only [cyclic_cubic_family_card_e6] at h <;> omega
  have hA_template : A = ({{1}, {0,1}, {3}, {0,4}, {3,4}, {1,5}, {0,1,5}, {2,5}, {2,3,5}, {0,4,5}} : Finset (Finset (Fin 6))).image (fun s => s.image (cyclic_cubic_family_card_e6 m)) := by
    simp only [A, Finset.image_insert, Finset.image_singleton]
    rfl
  have hAcard : A.card = 10 := by
    rw [hA_template, Finset.card_image_of_injective _ (Finset.image_injective hinj_e)]
    decide
  have hAcardle : ∀ S ∈ A, S.card ≤ 3 := by
    intro S hS
    simp only [A, Finset.mem_insert, Finset.mem_singleton] at hS
    rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  have hAnotB : ∀ S ∈ A, S ≠ ({m+1, m+4, m+5} : Finset ℕ) := by
    intro S hS
    simp only [A, Finset.mem_insert, Finset.mem_singleton] at hS
    rcases hS with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · intro h; have hh := Finset.ext_iff.mp h (m+5); simp at hh
    · intro h; have hh := Finset.ext_iff.mp h (m+5); simp at hh
    · intro h; have hh := Finset.ext_iff.mp h (m+5); simp at hh
    · intro h; have hh := Finset.ext_iff.mp h (m+5); simp at hh
    · intro h; have hh := Finset.ext_iff.mp h (m+5); simp at hh
    · intro h; have hh := Finset.ext_iff.mp h (m+4); simp at hh
    · intro h; have hh := Finset.ext_iff.mp h 0; simp at hh
    · intro h; have hh := Finset.ext_iff.mp h (m+4); simp at hh
    · intro h; have hh := Finset.ext_iff.mp h (m+2); simp at hh
    · intro h; have hh := Finset.ext_iff.mp h 0; simp at hh
  have hBmem : ∀ S, S ∈ B ↔ ∃ k, k ≤ m + 1 ∧ (S = insert k (Finset.Ico (k+3) (m+6)) ∨ S = insert k (insert (k+1) (Finset.Ico (k+3) (m+6)))) := by
    intro S
    simp only [B, Finset.mem_biUnion, Finset.mem_Iic, Finset.mem_insert, Finset.mem_singleton]
  have hBcard1 : ∀ k, k ≤ m + 1 → (insert k (Finset.Ico (k+3) (m+6)) : Finset ℕ).card = m + 4 - k := by
    intro k hk
    rw [Finset.card_insert_of_notMem (by simp [Finset.mem_Ico]), Nat.card_Ico]
    omega
  have hBcard2 : ∀ k, k ≤ m + 1 → (insert k (insert (k+1) (Finset.Ico (k+3) (m+6))) : Finset ℕ).card = m + 5 - k := by
    intro k hk
    rw [Finset.card_insert_of_notMem (by simp [Finset.mem_Ico]), Finset.card_insert_of_notMem (by simp [Finset.mem_Ico]), Nat.card_Ico]
    omega
  have hBge : ∀ S ∈ B, 3 ≤ S.card := by
    intro S hS
    rw [hBmem S] at hS
    obtain ⟨k, hk, rfl | rfl⟩ := hS
    · rw [hBcard1 k hk]; omega
    · rw [hBcard2 k hk]; omega
  have hBeq3 : ∀ S ∈ B, S.card = 3 → S = ({m+1, m+4, m+5} : Finset ℕ) := by
    intro S hS hc
    rw [hBmem S] at hS
    obtain ⟨k, hk, rfl | rfl⟩ := hS
    · rw [hBcard1 k hk] at hc
      have hk' : k = m + 1 := by omega
      subst hk'
      have hIco : Finset.Ico (m+1+3) (m+6) = ({m+4, m+5} : Finset ℕ) := by
        ext x; simp [Finset.mem_Ico]; omega
      rw [hIco]
    · rw [hBcard2 k hk] at hc
      omega
  have hBmiss : ∀ S ∈ B, ∃ k, k ≤ m + 1 ∧ k + 2 ∉ S := by
    intro S hS
    rw [hBmem S] at hS
    obtain ⟨k, hk, rfl | rfl⟩ := hS
    · exact ⟨k, hk, by intro h; simp only [Finset.mem_insert, Finset.mem_Ico] at h; omega⟩
    · exact ⟨k, hk, by intro h; simp only [Finset.mem_insert, Finset.mem_Ico] at h; omega⟩
  have hBcard : B.card = 2 * (m + 2) := by
    have hBpaircard : ∀ k, ({insert k (Finset.Ico (k+3) (m+6)), insert k (insert (k+1) (Finset.Ico (k+3) (m+6)))} : Finset (Finset ℕ)).card = 2 := by
      intro k
      have hne : (insert k (Finset.Ico (k+3) (m+6)) : Finset ℕ) ≠ insert k (insert (k+1) (Finset.Ico (k+3) (m+6))) := by
        intro h
        have hmem : k+1 ∈ insert k (insert (k+1) (Finset.Ico (k+3) (m+6))) := by simp
        rw [← h] at hmem
        simp only [Finset.mem_insert, Finset.mem_Ico] at hmem
        omega
      rw [Finset.card_insert_of_notMem (by simpa using hne), Finset.card_singleton]
    simp only [B]
    rw [Finset.card_biUnion]
    · rw [Finset.sum_congr rfl (fun k _ => hBpaircard k)]
      simp only [Finset.sum_const, Nat.card_Iic, smul_eq_mul]
      ring
    · intro k hk l hl hkl
      show Disjoint _ _
      rw [Finset.disjoint_left]
      intro S hS hT
      have hkS : k ∈ S ∧ ∀ x ∈ S, k ≤ x := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hS
        rcases hS with rfl | rfl
        · exact ⟨by simp, by intro x hx; simp only [Finset.mem_insert, Finset.mem_Ico] at hx; omega⟩
        · exact ⟨by simp, by intro x hx; simp only [Finset.mem_insert, Finset.mem_Ico] at hx; omega⟩
      have hlT : l ∈ S ∧ ∀ x ∈ S, l ≤ x := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at hT
        rcases hT with rfl | rfl
        · exact ⟨by simp, by intro x hx; simp only [Finset.mem_insert, Finset.mem_Ico] at hx; omega⟩
        · exact ⟨by simp, by intro x hx; simp only [Finset.mem_insert, Finset.mem_Ico] at hx; omega⟩
      obtain ⟨h1, h2⟩ := hkS
      obtain ⟨h3, h4⟩ := hlT
      have h1' : k ≤ l := h2 l h3
      have h2' : l ≤ k := h4 k h1
      omega
  have hCcard : C.card = 3 := by
    have h1 : Finset.Ico 2 (m+6) ∉ ({insert 0 (Finset.Ico 2 (m+6)), Finset.Iio (m+6)} : Finset (Finset ℕ)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      constructor
      · intro h; have := congrArg (fun s => (0:ℕ) ∈ s) h; simp at this
      · intro h; have := congrArg (fun s => (1:ℕ) ∈ s) h; simp at this
    have h2 : insert 0 (Finset.Ico 2 (m+6)) ∉ ({Finset.Iio (m+6)} : Finset (Finset ℕ)) := by
      simp only [Finset.mem_singleton]
      intro h; have := congrArg (fun s => (1:ℕ) ∈ s) h; simp at this
    simp only [C]
    rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2]
    rfl
  have hCge : ∀ S ∈ C, 4 ≤ S.card := by
    intro S hS
    simp only [C, Finset.mem_insert, Finset.mem_singleton] at hS
    rcases hS with rfl | rfl | rfl
    · rw [Nat.card_Ico]; omega
    · rw [Finset.card_insert_of_notMem (by simp [Finset.mem_Ico]), Nat.card_Ico]; omega
    · rw [Nat.card_Iio]; omega
  have hCsup : ∀ T ∈ C, Finset.Ico 2 (m+6) ⊆ T := by
    intro U hU
    simp only [C, Finset.mem_insert, Finset.mem_singleton] at hU
    rcases hU with rfl | rfl | rfl
    · exact Finset.Subset.refl _
    · intro x hx
      exact Finset.mem_insert_of_mem hx
    · intro x hx
      simp only [Finset.mem_Ico] at hx
      exact Finset.mem_Iio.mpr (by omega)
  have hbound : ∀ S ∈ A ∪ B ∪ C, ∀ x ∈ S, x < m + 6 := by
    intro S hS x hx
    simp only [Finset.mem_union] at hS
    rcases hS with (hSA | hSB) | hSC
    · simp only [A, Finset.mem_insert, Finset.mem_singleton] at hSA
      rcases hSA with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        (simp only [Finset.mem_insert, Finset.mem_singleton] at hx) <;> omega
    · rw [hBmem S] at hSB
      obtain ⟨k, hk, rfl | rfl⟩ := hSB <;>
        (simp only [Finset.mem_insert, Finset.mem_Ico] at hx) <;> omega
    · simp only [C, Finset.mem_insert, Finset.mem_singleton] at hSC
      rcases hSC with rfl | rfl | rfl <;>
        (simp only [Finset.mem_insert, Finset.mem_Ico, Finset.mem_Iio] at hx) <;> omega
  have hinj : Set.InjOn T ↑(A ∪ B ∪ C) := by
    intro S hS S' hS' h
    have h1 := hbound S hS
    have h2 := hbound S' hS'
    ext x
    constructor
    · intro hx
      have hmem : (⟨x, h1 x hx⟩ : Fin (m + 6)) ∈ T S := by simpa [T] using hx
      rw [h] at hmem
      simpa [T] using hmem
    · intro hx
      have hmem : (⟨x, h2 x hx⟩ : Fin (m + 6)) ∈ T S' := by simpa [T] using hx
      rw [← h] at hmem
      simpa [T] using hmem
  have hAC : Disjoint A C := by
    rw [Finset.disjoint_left]
    intro S hSA hSC
    have h1 := hAcardle S hSA
    have h2 := hCge S hSC
    omega
  have hAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro S hSA hSB
    have h1 := hAcardle S hSA
    have h2 := hBge S hSB
    have h3 : S.card = 3 := le_antisymm h1 h2
    exact hAnotB S hSA (hBeq3 S hSB h3)
  have hBC : Disjoint B C := by
    rw [Finset.disjoint_left]
    intro S hSB hSC
    obtain ⟨k, hk, hmiss⟩ := hBmiss S hSB
    exact hmiss (hCsup S hSC (by simp only [Finset.mem_Ico]; omega))
  have hABC : Disjoint (A ∪ B) C := Finset.disjoint_union_left.mpr ⟨hAC, hBC⟩
  rw [hfam, Finset.card_image_of_injOn hinj]
  rw [Finset.card_union_of_disjoint hABC, Finset.card_union_of_disjoint hAB, hAcard, hBcard, hCcard]
  omega
