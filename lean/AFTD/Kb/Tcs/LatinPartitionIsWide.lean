import AFTD.Prelude
import AFTD.Kb.Tcs.IsWidePartition
import AFTD.Kb.Tcs.IsLatinPartition
import AFTD.Kb.Tcs.IsLatinTableau
import AFTD.Kb.Tcs.YoungDiagramDominatesConjugate
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# latin_partition_is_wide

Topic: combinatorics   Node: 477aba85a01b

Provenance: formalization of a published result. Source: arXiv:2610.29291 Section 1

Every Latin Young diagram is wide: if a Young diagram $\mu$ admits a Latin tableau of shape $\mu$ and type $\mu'$ (`is_latin_partition μ`), then $\mu$ is wide (`is_wide_partition μ`).
-/

open YoungDiagram in
lemma latin_partition_is_wide_foldl_sum (f : ℕ → ℕ) (k : ℕ) :
    List.foldl (fun s r => s + f r) 0 (List.range k) = ∑ i ∈ Finset.range k, f i := by
  have h (l : List ℕ) (s : ℕ) : List.foldl (fun acc r => acc + f r) s l = s + (l.map f).sum := by
    induction l generalizing s with
    | nil => simp
    | cons x xs ih =>
      simp only [List.foldl_cons, List.map_cons, List.sum_cons]
      rw [ih, add_assoc]
  rw [h, zero_add]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

open YoungDiagram in
lemma latin_partition_is_wide_col_card (ν : YoungDiagram) (k : ℕ) :
    (ν.cells.filter (fun c => c.2 < k)).card = ∑ j ∈ Finset.range k, ν.colLen j := by
  let s := ν.cells.filter (fun c => c.2 < k)
  have hmaps : Set.MapsTo Prod.snd (s : Set (ℕ × ℕ)) (Finset.range k : Set ℕ) := by
    intro c hc
    simp only [s, Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hc ⊢
    exact hc.2
  have h := Finset.card_eq_sum_card_fiberwise (s := s) (t := Finset.range k) (f := Prod.snd) hmaps
  rw [h]
  apply Finset.sum_congr rfl
  intro j hj
  simp only [Finset.mem_range] at hj
  have hfiber : (s.filter (fun c => c.2 = j)) = ν.col j := by
    ext ⟨a, b⟩
    simp only [s, Finset.mem_filter, mem_cells, mem_col_iff]
    constructor
    · rintro ⟨⟨h1, _⟩, rfl⟩
      exact ⟨h1, rfl⟩
    · rintro ⟨h1, rfl⟩
      exact ⟨⟨h1, hj⟩, rfl⟩
  rw [hfiber, colLen_eq_card]

open YoungDiagram in
lemma latin_partition_is_wide_row_min_sum (ν : YoungDiagram) (k : ℕ) :
    (ν.cells.filter (fun c => c.2 < k)).card = ∑ i ∈ Finset.range (ν.colLen 0), min (ν.rowLen i) k := by
  let s := ν.cells.filter (fun c => c.2 < k)
  have hmaps : Set.MapsTo Prod.fst (s : Set (ℕ × ℕ)) (Finset.range (ν.colLen 0) : Set ℕ) := by
    intro c hc
    simp only [s, Finset.mem_coe, Finset.mem_filter, Finset.mem_range, mem_cells] at hc ⊢
    rw [mem_iff_lt_colLen] at hc
    exact hc.1.trans_le (ν.colLen_anti 0 c.2 (Nat.zero_le c.2))
  have h := Finset.card_eq_sum_card_fiberwise (s := s) (t := Finset.range (ν.colLen 0)) (f := Prod.fst) hmaps
  rw [h]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Finset.mem_range] at hi
  have hfiber : (s.filter (fun c => c.1 = i)) = {i} ×ˢ Finset.range (min (ν.rowLen i) k) := by
    ext ⟨a, b⟩
    simp only [s, Finset.mem_filter, mem_cells, Finset.mem_product, Finset.mem_singleton,
      Finset.mem_range, mem_iff_lt_rowLen, lt_min_iff]
    aesop
  rw [hfiber, Finset.card_product, Finset.card_singleton, Finset.card_range, one_mul]

open YoungDiagram in
lemma latin_partition_is_wide_sum_col_eq_sum_min_row (ν : YoungDiagram) (k : ℕ) :
    ∑ j ∈ Finset.range k, ν.colLen j = ∑ i ∈ Finset.range (ν.colLen 0), min (ν.rowLen i) k := by
  rw [← latin_partition_is_wide_col_card, latin_partition_is_wide_row_min_sum]

open YoungDiagram in
lemma latin_partition_is_wide_sum_row_eq_sum_min_col (ν : YoungDiagram) (k : ℕ) :
    ∑ i ∈ Finset.range k, ν.rowLen i = ∑ j ∈ Finset.range (ν.rowLen 0), min (ν.colLen j) k := by
  have h := latin_partition_is_wide_sum_col_eq_sum_min_row ν.transpose k
  simp only [colLen_transpose, rowLen_transpose] at h
  exact h

open YoungDiagram in
lemma latin_partition_is_wide_sublist_embed {α : Type*} : ∀ {l₁ l₂ : List α}, l₁.Sublist l₂ →
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ (∀ i < l₁.length, l₂[φ i]? = l₁[i]?)
  | [], [], List.Sublist.slnil => by
    refine ⟨id, strictMono_id, fun i hi => (Nat.not_lt_zero i hi).elim⟩
  | l₁, a :: l₂, List.Sublist.cons _ h => by
    obtain ⟨φ, hφ_mono, hφ_eq⟩ := latin_partition_is_wide_sublist_embed h
    refine ⟨Nat.succ ∘ φ, strictMono_nat_of_lt_succ fun n => ?_, fun i hi => ?_⟩
    · simp only [Function.comp_apply]
      exact Nat.succ_lt_succ (hφ_mono (Nat.lt_succ_self n))
    · simp only [Function.comp_apply, List.getElem?_cons_succ]
      exact hφ_eq i hi
  | _, _, List.Sublist.cons_cons a h => by
    obtain ⟨φ, hφ_mono, hφ_eq⟩ := latin_partition_is_wide_sublist_embed h
    let φ' : ℕ → ℕ := fun n => match n with
      | 0 => 0
      | n + 1 => φ n + 1
    refine ⟨φ', strictMono_nat_of_lt_succ fun n => ?_, fun i hi => ?_⟩
    · cases n
      · simp only [φ', Nat.zero_lt_succ]
      · simp only [φ', add_lt_add_iff_right]
        exact hφ_mono (Nat.lt_succ_self _)
    · cases i
      · simp [φ']
      · simp only [List.length_cons, Nat.succ_lt_succ_iff] at hi
        simp only [φ', List.getElem?_cons_succ]
        exact hφ_eq _ hi

open YoungDiagram in
lemma latin_partition_is_wide_perm_filter (m k : ℕ) (g : ℕ → ℕ)
    (hg_maps : ∀ j < m, 1 ≤ g j ∧ g j ≤ m)
    (hg_inj : ∀ j₁ < m, ∀ j₂ < m, g j₁ = g j₂ → j₁ = j₂) :
    ((Finset.range m).filter (fun j => g j ≤ k)).card = min m k := by
  let s := Finset.range m
  let t := Finset.Ioc 0 m
  have ht_card : t.card = m := Nat.card_Ioc 0 m
  have h_img_sub : s.image g ⊆ t := by
    intro y hy
    rw [Finset.mem_image] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    rw [Finset.mem_range] at hx
    simp only [t, Finset.mem_Ioc]
    have := hg_maps x hx
    omega
  have h_img_card : (s.image g).card = m := by
    rw [Finset.card_image_of_injOn]
    · simp [s]
    · intro x hx y hy hxy
      rw [Finset.mem_coe, Finset.mem_range] at hx hy
      exact hg_inj x hx y hy hxy
  have h_img_eq : s.image g = t := by
    apply Finset.eq_of_subset_of_card_le h_img_sub
    rw [h_img_card, ht_card]
  have h_filter_img : ((s.filter (fun j => g j ≤ k)).image g) = t.filter (fun v => v ≤ k) := by
    ext v
    simp only [Finset.mem_image, Finset.mem_filter, s, Finset.mem_range]
    constructor
    · rintro ⟨j, ⟨hj, hgj⟩, rfl⟩
      have := hg_maps j hj
      simp only [t, Finset.mem_Ioc]
      omega
    · rintro ⟨hv_t, hvk⟩
      have hv_img : v ∈ s.image g := by rw [h_img_eq]; exact hv_t
      rw [Finset.mem_image] at hv_img
      obtain ⟨j, hj, rfl⟩ := hv_img
      rw [Finset.mem_range] at hj
      exact ⟨j, ⟨hj, hvk⟩, rfl⟩
  have h_inj_filter : Set.InjOn g ((s.filter (fun j => g j ≤ k)) : Set ℕ) := by
    intro x hx y hy hxy
    rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hx hy
    exact hg_inj x hx.1 y hy.1 hxy
  have h_card_eq : ((s.filter (fun j => g j ≤ k)).image g).card = (s.filter (fun j => g j ≤ k)).card :=
    Finset.card_image_of_injOn h_inj_filter
  rw [← h_card_eq, h_filter_img]
  have h_ioc : (t.filter (fun v => v ≤ k)) = Finset.Ioc 0 (min m k) := by
    ext v
    simp only [t, Finset.mem_filter, Finset.mem_Ioc, le_min_iff]
    omega
  rw [h_ioc, Nat.card_Ioc, Nat.sub_zero]

open YoungDiagram in
lemma latin_partition_is_wide_col_filter_le (m k : ℕ) (h : ℕ → ℕ)
    (hh_maps : ∀ i < m, 1 ≤ h i)
    (hh_inj : ∀ i₁ < m, ∀ i₂ < m, h i₁ = h i₂ → i₁ = i₂) :
    ((Finset.range m).filter (fun i => h i ≤ k)).card ≤ min m k := by
  let s := (Finset.range m).filter (fun i => h i ≤ k)
  have h1 : s.card ≤ m := by
    have : s ⊆ Finset.range m := Finset.filter_subset _ _
    exact (Finset.card_le_card this).trans_eq (Finset.card_range m)
  have h2 : s.card ≤ k := by
    have h_maps : Set.MapsTo h (s : Set ℕ) (Finset.Ioc 0 k : Set ℕ) := by
      intro i hi
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hi
      simp only [Finset.mem_coe, Finset.mem_Ioc]
      have := hh_maps i hi.1
      omega
    have h_inj : Set.InjOn h (s : Set ℕ) := by
      intro x hx y hy hxy
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hx hy
      exact hh_inj x hx.1 y hy.1 hxy
    have := Finset.card_le_card_of_injOn h h_maps h_inj
    rwa [Nat.card_Ioc, Nat.sub_zero] at this
  exact le_min h1 h2

/-- Every Latin partition is wide. -/
theorem latin_partition_is_wide (μ : YoungDiagram) (h : is_latin_partition μ) : is_wide_partition μ := by
  obtain ⟨T, hT⟩ := h
  intro ν hsub
  obtain ⟨φ, hφ_mono, hφ_eq⟩ := latin_partition_is_wide_sublist_embed hsub
  have hφ_row : ∀ i < ν.colLen 0, φ i < μ.colLen 0 ∧ ν.rowLen i = μ.rowLen (φ i) := by
    intro i hi
    rw [← YoungDiagram.length_rowLens] at hi
    have h_opt := hφ_eq i hi
    have h_some : ν.rowLens[i]? = some ν.rowLens[i] := List.getElem?_eq_getElem hi
    rw [h_some] at h_opt
    have h_len : φ i < μ.rowLens.length := by
      by_contra h_ge
      rw [List.getElem?_eq_none (not_lt.mp h_ge)] at h_opt
      contradiction
    have h_val : μ.rowLens[φ i] = ν.rowLens[i] := by
      have := List.getElem?_eq_getElem h_len
      rw [h_opt] at this
      exact Option.some_injective _ this.symm
    rw [YoungDiagram.length_rowLens] at h_len
    rw [YoungDiagram.get_rowLens, YoungDiagram.get_rowLens] at h_val
    exact ⟨h_len, h_val.symm⟩
  have hcell_mem : ∀ {i j : ℕ}, (i, j) ∈ ν → (φ i, j) ∈ μ := by
    intro i j hcell
    have hi : i < ν.colLen 0 := by
      rw [YoungDiagram.mem_iff_lt_colLen] at hcell
      exact hcell.trans_le (ν.colLen_anti 0 j (Nat.zero_le j))
    have hlen := (hφ_row i hi).2
    rw [YoungDiagram.mem_iff_lt_rowLen] at hcell ⊢
    rwa [← hlen]
  intro k
  simp only [ge_iff_le]
  rw [latin_partition_is_wide_foldl_sum, latin_partition_is_wide_foldl_sum]
  let S := ν.cells.filter (fun c => T (φ c.1) c.2 ≤ k)
  have hmaps_row : Set.MapsTo Prod.fst (S : Set (ℕ × ℕ)) (Finset.range (ν.colLen 0) : Set ℕ) := by
    intro c hc
    rw [Finset.mem_coe, Finset.mem_filter, YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_colLen] at hc
    rw [Finset.mem_coe, Finset.mem_range]
    exact hc.1.trans_le (ν.colLen_anti 0 c.2 (Nat.zero_le c.2))
  have hmaps_col : Set.MapsTo Prod.snd (S : Set (ℕ × ℕ)) (Finset.range (ν.rowLen 0) : Set ℕ) := by
    intro c hc
    rw [Finset.mem_coe, Finset.mem_filter, YoungDiagram.mem_cells, YoungDiagram.mem_iff_lt_rowLen] at hc
    rw [Finset.mem_coe, Finset.mem_range]
    exact hc.1.trans_le (ν.rowLen_anti 0 c.1 (Nat.zero_le c.1))
  have hS_row : S.card = ∑ i ∈ Finset.range (ν.colLen 0), min (ν.rowLen i) k := by
    rw [Finset.card_eq_sum_card_fiberwise (s := S) (t := Finset.range (ν.colLen 0)) (f := Prod.fst) hmaps_row]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_range] at hi
    have hfib : (S.filter (fun c => c.1 = i)) = {i} ×ˢ ((Finset.range (ν.rowLen i)).filter (fun j => T (φ i) j ≤ k)) := by
      ext ⟨a, b⟩
      simp only [S, Finset.mem_filter, YoungDiagram.mem_cells, Finset.mem_product, Finset.mem_singleton,
        Finset.mem_range, YoungDiagram.mem_iff_lt_rowLen]
      aesop
    rw [hfib, Finset.card_product, Finset.card_singleton, one_mul]
    apply latin_partition_is_wide_perm_filter
    · intro j hj
      have hc : (i, j) ∈ ν := by rwa [YoungDiagram.mem_iff_lt_rowLen]
      have hc_μ := hcell_mem hc
      have h1 := hT.1 hc_μ
      have hlen := (hφ_row i hi).2
      rwa [← hlen] at h1
    · intro j₁ hj₁ j₂ hj₂ heq
      have hc₁ : (i, j₁) ∈ ν := by rwa [YoungDiagram.mem_iff_lt_rowLen]
      have hc₂ : (i, j₂) ∈ ν := by rwa [YoungDiagram.mem_iff_lt_rowLen]
      exact hT.2.1 (hcell_mem hc₁) (hcell_mem hc₂) heq
  have hS_col : S.card ≤ ∑ j ∈ Finset.range (ν.rowLen 0), min (ν.colLen j) k := by
    rw [Finset.card_eq_sum_card_fiberwise (s := S) (t := Finset.range (ν.rowLen 0)) (f := Prod.snd) hmaps_col]
    apply Finset.sum_le_sum
    intro j hj
    simp only [Finset.mem_range] at hj
    have hfib : (S.filter (fun c => c.2 = j)) = ((Finset.range (ν.colLen j)).filter (fun i => T (φ i) j ≤ k)) ×ˢ {j} := by
      ext ⟨a, b⟩
      simp only [S, Finset.mem_filter, YoungDiagram.mem_cells, Finset.mem_product, Finset.mem_singleton,
        Finset.mem_range, YoungDiagram.mem_iff_lt_colLen]
      aesop
    rw [hfib, Finset.card_product, Finset.card_singleton, mul_one]
    apply latin_partition_is_wide_col_filter_le
    · intro i hi
      have hc : (i, j) ∈ ν := by rwa [YoungDiagram.mem_iff_lt_colLen]
      exact (hT.1 (hcell_mem hc)).1
    · intro i₁ hi₁ i₂ hi₂ heq
      have hc₁ : (i₁, j) ∈ ν := by rwa [YoungDiagram.mem_iff_lt_colLen]
      have hc₂ : (i₂, j) ∈ ν := by rwa [YoungDiagram.mem_iff_lt_colLen]
      have h_phi_eq := hT.2.2 (hcell_mem hc₁) (hcell_mem hc₂) heq
      exact hφ_mono.injective h_phi_eq
  rw [latin_partition_is_wide_sum_col_eq_sum_min_row, latin_partition_is_wide_sum_row_eq_sum_min_col]
  linarith
