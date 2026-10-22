import AFTD.Prelude
import AFTD.Kb.Tcs.Op258HasMonoClique
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# op_258_has_mono_clique_of_bounded_colors

Topic: combinatorics   Node: 0baf63568f79

Provenance: helper lemma. step towards op_258_forces_step

For any clique size k ≥ 1 and colour bound C ≥ 1, there exists N such that for all n ≥ N, every edge colouring of K_n with colors at most C contains a monochromatic K_k.
-/

def op_258_has_mono_clique_of_bounded_colors_bound (C : ℕ) : ℕ → ℕ
  | 0 => 1
  | m + 1 => C * op_258_has_mono_clique_of_bounded_colors_bound C m + 1

lemma op_258_has_mono_clique_of_bounded_colors_one_le_bound (C m : ℕ) :
    1 ≤ op_258_has_mono_clique_of_bounded_colors_bound C m := by
  cases m <;> simp [op_258_has_mono_clique_of_bounded_colors_bound]

lemma op_258_has_mono_clique_of_bounded_colors_fin_cases_of_lt {m : ℕ} (i j : Fin (m + 1)) (hij : i < j) :
    (i = 0 ∧ ∃ j' : Fin m, j = j'.succ) ∨
    (∃ (i' j' : Fin m), i = i'.succ ∧ j = j'.succ ∧ i' < j') := by
  induction i using Fin.cases with
  | zero =>
    left
    refine ⟨rfl, ?_⟩
    induction j using Fin.cases with
    | zero => exact False.elim (lt_irrefl 0 hij)
    | succ j' => exact ⟨j', rfl⟩
  | succ i' =>
    right
    induction j using Fin.cases with
    | zero => exact False.elim (Fin.not_lt_zero i'.succ hij)
    | succ j' =>
      refine ⟨i', j', rfl, rfl, Fin.succ_lt_succ_iff.mp hij⟩

lemma op_258_has_mono_clique_of_bounded_colors_php {α : Type*} [DecidableEq α] (s : Finset α)
    (C B : ℕ) (hC : 1 ≤ C) (f : α → ℕ) (hf : ∀ a ∈ s, f a ∈ Finset.Icc 1 C) (hs : C * B ≤ s.card) :
    ∃ y ∈ Finset.Icc 1 C, B ≤ (s.filter (fun x => f x = y)).card := by
  have ht_nonempty : (Finset.Icc 1 C).Nonempty := ⟨1, by simp [hC]⟩
  have ht_card : (Finset.Icc 1 C).card = C := by simp [Nat.card_Icc]
  have h_le : (Finset.Icc 1 C).card * B ≤ s.card := by
    rw [ht_card]
    exact hs
  obtain ⟨y, hy, hB⟩ := Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to hf ht_nonempty h_le
  exact ⟨y, hy, hB⟩

lemma op_258_has_mono_clique_of_bounded_colors_sequence (n C : ℕ) (hC : 1 ≤ C)
    (c : (SimpleGraph.completeGraph (Fin n)).edgeSet → ℕ+)
    (hc : ∀ e, (c e : ℕ) ≤ C) (m : ℕ) :
    ∀ (V : Finset (Fin n)) (_hV : op_258_has_mono_clique_of_bounded_colors_bound C m ≤ V.card),
      ∃ (v : Fin m → Fin n) (col : Fin m → ℕ+) (V' : Finset (Fin n)),
        (∀ i, (col i : ℕ) ≤ C) ∧
        (∀ i, v i ∈ V) ∧
        V' ⊆ V ∧
        (∀ i, v i ∉ V') ∧
        Function.Injective v ∧
        (∀ (i j : Fin m) (_hij : i < j) (h : v i ≠ v j),
          c ⟨s(v i, v j), by simp [SimpleGraph.completeGraph_eq_top, h]⟩ = col i) ∧
        (∀ (i : Fin m) (w : Fin n) (_hw : w ∈ V') (h : v i ≠ w),
          c ⟨s(v i, w), by simp [SimpleGraph.completeGraph_eq_top, h]⟩ = col i) := by
  induction m with
  | zero =>
    intro V _
    refine ⟨Fin.elim0, Fin.elim0, V, ?_⟩
    refine ⟨by intro i; exact Fin.elim0 i,
            by intro i; exact Fin.elim0 i,
            Finset.Subset.refl V,
            by intro i; exact Fin.elim0 i,
            by intro i; exact Fin.elim0 i,
            by intro i; exact Fin.elim0 i,
            by intro i; exact Fin.elim0 i⟩
  | succ m ih =>
    intro V hV
    have hV_pos : 0 < V.card := by
      have := op_258_has_mono_clique_of_bounded_colors_one_le_bound C (m + 1)
      omega
    obtain ⟨x, hx⟩ := Finset.card_pos.mp hV_pos
    let V0 := V.erase x
    have hV0_card : C * op_258_has_mono_clique_of_bounded_colors_bound C m ≤ V0.card := by
      simp only [V0, Finset.card_erase_of_mem hx]
      simp only [op_258_has_mono_clique_of_bounded_colors_bound] at hV
      omega
    let f : Fin n → ℕ := fun w =>
      if hw : x = w then 1
      else (c ⟨s(x, w), by simp [SimpleGraph.completeGraph_eq_top, hw]⟩ : ℕ)
    have hf : ∀ w ∈ V0, f w ∈ Finset.Icc 1 C := by
      intro w hw
      have hw_ne : x ≠ w := (Finset.mem_erase.mp hw).1.symm
      dsimp [f]
      split_ifs with h
      · contradiction
      · simp only [Finset.mem_Icc]
        refine ⟨(c _).prop, hc _⟩
    obtain ⟨y, hy, hW_card⟩ := op_258_has_mono_clique_of_bounded_colors_php V0 C
      (op_258_has_mono_clique_of_bounded_colors_bound C m) hC f hf hV0_card
    have hy_pos : 0 < y := (Finset.mem_Icc.mp hy).1
    have hy_le : y ≤ C := (Finset.mem_Icc.mp hy).2
    let y_p : ℕ+ := ⟨y, hy_pos⟩
    let W := V0.filter (fun w => f w = y)
    obtain ⟨v, col, V', hcol_le, hv_mem, hV'_sub, hv_not_mem, hv_inj, hedge_col, hedge_V'⟩ :=
      ih W hW_card
    have hW_sub_V0 : W ⊆ V0 := Finset.filter_subset _ _
    have hV0_sub_V : V0 ⊆ V := Finset.erase_subset x V
    have hW_sub_V : W ⊆ V := hW_sub_V0.trans hV0_sub_V
    have hx_not_V0 : x ∉ V0 := by simp [V0]
    have hx_not_W : x ∉ W := fun h => hx_not_V0 (hW_sub_V0 h)
    have hx_not_V' : x ∉ V' := fun h => hx_not_W (hV'_sub h)
    let v_new : Fin (m + 1) → Fin n := Fin.cons x v
    let col_new : Fin (m + 1) → ℕ+ := Fin.cons y_p col
    refine ⟨v_new, col_new, V', ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i
      induction i using Fin.cases with
      | zero => exact hy_le
      | succ i' => exact hcol_le i'
    · intro i
      induction i using Fin.cases with
      | zero => exact hx
      | succ i' => exact hW_sub_V (hv_mem i')
    · exact hV'_sub.trans hW_sub_V
    · intro i
      induction i using Fin.cases with
      | zero => exact hx_not_V'
      | succ i' => exact hv_not_mem i'
    · intro i j hij
      induction i using Fin.cases with
      | zero =>
        induction j using Fin.cases with
        | zero => rfl
        | succ j' =>
          have hv_in : v j' ∈ W := hv_mem j'
          change x = v j' at hij
          exfalso
          exact hx_not_W (hij ▸ hv_in)
      | succ i' =>
        induction j using Fin.cases with
        | zero =>
          have hv_in : v i' ∈ W := hv_mem i'
          change v i' = x at hij
          exfalso
          exact hx_not_W (hij.symm ▸ hv_in)
        | succ j' =>
          change v i' = v j' at hij
          exact congrArg Fin.succ (hv_inj hij)
    · intro i j hij h_ne
      rcases op_258_has_mono_clique_of_bounded_colors_fin_cases_of_lt i j hij with (⟨rfl, j', rfl⟩ | ⟨i', j', rfl, rfl, hlt⟩)
      · have hv_in : v j' ∈ W := hv_mem j'
        have hv_f : f (v j') = y := (Finset.mem_filter.mp hv_in).2
        have h_x_ne : x ≠ v j' := by
          intro h_eq
          exact hx_not_W (h_eq ▸ hv_in)
        dsimp [f] at hv_f
        split_ifs at hv_f with h_if
        · contradiction
        · apply Subtype.ext
          exact hv_f
      · have h_ne' : v i' ≠ v j' := by
          intro heq
          have := hv_inj heq
          exact ne_of_lt hlt this
        exact hedge_col i' j' hlt h_ne'
    · intro i w hw h_ne
      induction i using Fin.cases with
      | zero =>
        have hw_in : w ∈ W := hV'_sub hw
        have hw_f : f w = y := (Finset.mem_filter.mp hw_in).2
        have h_x_ne : x ≠ w := by
          intro h_eq
          exact hx_not_W (h_eq ▸ hw_in)
        dsimp [f] at hw_f
        split_ifs at hw_f with h_if
        · contradiction
        · apply Subtype.ext
          exact hw_f
      | succ i' =>
        have h_ne' : v i' ≠ w := by
          intro heq
          have : v i' ∈ V' := heq ▸ hw
          exact hv_not_mem i' this
        exact hedge_V' i' w hw h_ne'

/-- For any clique size k ≥ 1 and colour bound C ≥ 1, on sufficiently large complete graphs K_n, every edge colouring using colours {1, …, C} has a monochromatic K_k (finite Ramsey theorem). -/
theorem op_258_has_mono_clique_of_bounded_colors (k C : ℕ) (hk : 1 ≤ k) (hC : 1 ≤ C) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ c : (SimpleGraph.completeGraph (Fin n)).edgeSet → ℕ+,
      (∀ e, (c e : ℕ) ≤ C) → op_258_has_mono_clique n c k := by
  let m := C * (k - 1) + 1
  use op_258_has_mono_clique_of_bounded_colors_bound C m
  intro n hn c hc
  have hV : op_258_has_mono_clique_of_bounded_colors_bound C m ≤ (Finset.univ : Finset (Fin n)).card := by
    simp only [Finset.card_univ, Fintype.card_fin]
    exact hn
  obtain ⟨v, col, V', hcol_le, -, -, -, hv_inj, hedge_col, -⟩ :=
    op_258_has_mono_clique_of_bounded_colors_sequence n C hC c hc m Finset.univ hV
  let f : Fin m → ℕ := fun i => (col i : ℕ)
  have hf : ∀ i, f i ∈ Finset.Icc 1 C := by
    intro i
    simp only [f, Finset.mem_Icc]
    exact ⟨(col i).prop, hcol_le i⟩
  have ht_card : (Finset.Icc 1 C).card = C := by simp [Nat.card_Icc]
  have h_lt : (Finset.Icc 1 C).card * (k - 1) < (Finset.univ : Finset (Fin m)).card := by
    rw [ht_card]
    simp only [Finset.card_univ, Fintype.card_fin, m]
    omega
  obtain ⟨y, hy, hlt⟩ :=
    Finset.exists_lt_card_fiber_of_mul_lt_card_of_maps_to (fun a _ => hf a) h_lt
  have hk_le : k ≤ (Finset.univ.filter (fun x => f x = y)).card := by omega
  obtain ⟨I', hI'_sub, hI'_card⟩ := Finset.exists_subset_card_eq hk_le
  let s := I'.image v
  have hs_card : s.card = k := by
    rw [Finset.card_image_of_injective I' hv_inj, hI'_card]
  have hy_pos : 0 < y := (Finset.mem_Icc.mp hy).1
  let y_p : ℕ+ := ⟨y, hy_pos⟩
  unfold op_258_has_mono_clique
  use s, y_p
  refine ⟨hs_card, ?_⟩
  intro u w hu hw huw
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hw
  have hij_ne : i ≠ j := by
    intro heq
    subst heq
    contradiction
  have hi_col : col i = y_p := by
    have : f i = y := (Finset.mem_filter.mp (hI'_sub hi)).2
    apply Subtype.ext
    exact this
  have hj_col : col j = y_p := by
    have : f j = y := (Finset.mem_filter.mp (hI'_sub hj)).2
    apply Subtype.ext
    exact this
  rcases lt_or_gt_of_ne hij_ne with (hlt | hgt)
  · have := hedge_col i j hlt huw
    rw [this, hi_col]
  · have h_symm : (⟨s(v i, v j), by simp [SimpleGraph.completeGraph_eq_top, huw]⟩ :
        (SimpleGraph.completeGraph (Fin n)).edgeSet) =
        ⟨s(v j, v i), by simp [SimpleGraph.completeGraph_eq_top, huw.symm]⟩ := by
      apply Subtype.ext
      exact Sym2.eq_swap
    rw [h_symm]
    have := hedge_col j i hgt huw.symm
    rw [this, hj_col]
