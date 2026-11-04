import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphCsymMaxNullity
import AFTD.Kb.Tcs.SimpleGraphFortTransversalNumber
import AFTD.Kb.Tcs.IsCsymMatrix
import AFTD.Kb.Tcs.IsCompatibleCollection
import AFTD.Kb.Tcs.SimpleGraphIsFort
import AFTD.Kb.Tcs.FinsetTransversalNumber

/-!
# op_979_csym_max_nullity_le_fort_transversal_number

Topic: graphs   Node: 791f48475dec

Provenance: formalization of a published result. Source: arXiv:2611.01102 Sec. 2, Theorem 2.10

For every finite simple graph G on a finite type V with decidable equality, the combinatorially symmetric maximum nullity N(G) is at most the fort transversal number T(G).
-/

open Classical in
noncomputable def op_979_csym_max_nullity_le_fort_transversal_number_vec_supp
    {V : Type*} [Fintype V] (x : V → ℝ) : Finset V :=
  Finset.filter (fun v => x v ≠ 0) Finset.univ

open Classical in
noncomputable def op_979_csym_max_nullity_le_fort_transversal_number_kernel_supports
    {V : Type*} [Fintype V] (A : Matrix V V ℝ) : Finset (Finset V) :=
  Finset.filter (fun s => ∃ x ∈ A.mulVecLin.ker, x ≠ 0 ∧
    op_979_csym_max_nullity_le_fort_transversal_number_vec_supp x = s) Finset.univ

open Classical in
lemma op_979_csym_max_nullity_le_fort_transversal_number_mem_vec_supp_iff
    {V : Type*} [Fintype V] {x : V → ℝ} {v : V} :
    v ∈ op_979_csym_max_nullity_le_fort_transversal_number_vec_supp x ↔ x v ≠ 0 := by
  simp [op_979_csym_max_nullity_le_fort_transversal_number_vec_supp]

open Classical in
lemma op_979_csym_max_nullity_le_fort_transversal_number_vec_supp_eq_empty_iff
    {V : Type*} [Fintype V] {x : V → ℝ} :
    op_979_csym_max_nullity_le_fort_transversal_number_vec_supp x = ∅ ↔ x = 0 := by
  simp [op_979_csym_max_nullity_le_fort_transversal_number_vec_supp, Finset.filter_eq_empty_iff, funext_iff]

open Classical in
lemma op_979_csym_max_nullity_le_fort_transversal_number_vec_supp_nonempty_iff
    {V : Type*} [Fintype V] {x : V → ℝ} :
    (op_979_csym_max_nullity_le_fort_transversal_number_vec_supp x).Nonempty ↔ x ≠ 0 := by
  rw [Finset.nonempty_iff_ne_empty, not_iff_not,
    op_979_csym_max_nullity_le_fort_transversal_number_vec_supp_eq_empty_iff]

open Classical in
lemma op_979_csym_max_nullity_le_fort_transversal_number_kernel_supports_is_fort
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} {A : Matrix V V ℝ}
    (hA : is_csym_matrix G A) {s : Finset V}
    (hs : s ∈ op_979_csym_max_nullity_le_fort_transversal_number_kernel_supports A) :
    simple_graph_is_fort G (s : Set V) := by
  rw [op_979_csym_max_nullity_le_fort_transversal_number_kernel_supports, Finset.mem_filter] at hs
  rcases hs.2 with ⟨x, hx_ker, hx_ne, rfl⟩
  rw [simple_graph_is_fort]
  refine ⟨?_, ?_⟩
  · rw [Finset.coe_nonempty,
        op_979_csym_max_nullity_le_fort_transversal_number_vec_supp_nonempty_iff]
    exact hx_ne
  · intro v hv
    rw [Finset.mem_coe,
        op_979_csym_max_nullity_le_fort_transversal_number_mem_vec_supp_iff, not_not] at hv
    rintro ⟨u, ⟨hu_s, hu_adj⟩, hu_uniq⟩
    rw [Finset.mem_coe,
        op_979_csym_max_nullity_le_fort_transversal_number_mem_vec_supp_iff] at hu_s
    have hx_ker_v : (A.mulVecLin x) v = 0 := by
      have : x ∈ LinearMap.ker A.mulVecLin := hx_ker
      rw [LinearMap.mem_ker] at this
      rw [this]
      rfl
    have hmul : (A.mulVecLin x) v = ∑ w, A v w * x w := rfl
    rw [hmul] at hx_ker_v
    have hterm : ∀ w, w ≠ u → A v w * x w = 0 := by
      intro w hw
      by_cases hxw : x w = 0
      · rw [hxw, mul_zero]
      · have hws : w ∈ op_979_csym_max_nullity_le_fort_transversal_number_vec_supp x :=
          op_979_csym_max_nullity_le_fort_transversal_number_mem_vec_supp_iff.mpr hxw
        have hnotadj : ¬ G.Adj v w := by
          intro hadj
          have : w = u := hu_uniq w ⟨hws, hadj⟩
          exact hw this
        have hne : v ≠ w := by
          rintro rfl
          exact hxw hv
        have hAvw : A v w = 0 := by
          have := (hA.2 v w hne).not.mpr hnotadj
          exact not_not.mp this
        rw [hAvw, zero_mul]
    rw [Finset.sum_eq_single u (fun w _ hw => hterm w hw)
      (fun hu => False.elim (hu (Finset.mem_univ u)))] at hx_ker_v
    have hne_vu : v ≠ u := by
      rintro rfl
      exact hu_s hv
    have hAvu : A v u ≠ 0 := (hA.2 v u hne_vu).mpr hu_adj
    exact mul_ne_zero hAvu hu_s hx_ker_v

open Classical in
lemma op_979_csym_max_nullity_le_fort_transversal_number_kernel_supports_compatible
    {V : Type*} [Fintype V] [DecidableEq V] (A : Matrix V V ℝ) :
    is_compatible_collection (op_979_csym_max_nullity_le_fort_transversal_number_kernel_supports A) := by
  intro C1 hC1 C2 hC2 hne v0 hv0
  rw [op_979_csym_max_nullity_le_fort_transversal_number_kernel_supports, Finset.mem_filter] at hC1 hC2
  rcases hC1.2 with ⟨x1, hx1_ker, hx1_ne, rfl⟩
  rcases hC2.2 with ⟨x2, hx2_ker, hx2_ne, rfl⟩
  rw [Finset.mem_inter] at hv0
  have hv1 : x1 v0 ≠ 0 :=
    op_979_csym_max_nullity_le_fort_transversal_number_mem_vec_supp_iff.mp hv0.1
  have hv2 : x2 v0 ≠ 0 :=
    op_979_csym_max_nullity_le_fort_transversal_number_mem_vec_supp_iff.mp hv0.2
  let y : V → ℝ := (x2 v0) • x1 - (x1 v0) • x2
  have hy_ker : y ∈ LinearMap.ker A.mulVecLin := by
    exact Submodule.sub_mem _ (Submodule.smul_mem _ _ hx1_ker) (Submodule.smul_mem _ _ hx2_ker)
  have hy_ne : y ≠ 0 := by
    intro hy_zero
    have h_prop : ∀ w, x1 w = (x1 v0 / x2 v0) * x2 w := by
      intro w
      have hy_w : y w = 0 := congr_fun hy_zero w
      dsimp [y] at hy_w
      have : x2 v0 * x1 w = x1 v0 * x2 w := by linarith
      calc x1 w = (x2 v0 * x1 w) / x2 v0 := by rw [mul_div_cancel_left₀ (x1 w) hv2]
      _ = (x1 v0 * x2 w) / x2 v0 := by rw [this]
      _ = (x1 v0 / x2 v0) * x2 w := by ring
    have h_same_supp : op_979_csym_max_nullity_le_fort_transversal_number_vec_supp x1 =
        op_979_csym_max_nullity_le_fort_transversal_number_vec_supp x2 := by
      ext w
      simp only [op_979_csym_max_nullity_le_fort_transversal_number_mem_vec_supp_iff]
      have hc : x1 v0 / x2 v0 ≠ 0 := div_ne_zero hv1 hv2
      rw [h_prop w, mul_ne_zero_iff]
      simp [hc]
    exact hne h_same_supp
  refine ⟨op_979_csym_max_nullity_le_fort_transversal_number_vec_supp y, ?_, ?_⟩
  · rw [op_979_csym_max_nullity_le_fort_transversal_number_kernel_supports, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ⟨y, hy_ker, hy_ne, rfl⟩⟩
  · intro w hw
    rw [op_979_csym_max_nullity_le_fort_transversal_number_mem_vec_supp_iff] at hw
    rw [Finset.mem_sdiff, Finset.mem_union, Finset.mem_singleton]
    refine ⟨?_, ?_⟩
    · by_contra hnot
      rw [not_or, op_979_csym_max_nullity_le_fort_transversal_number_mem_vec_supp_iff,
          op_979_csym_max_nullity_le_fort_transversal_number_mem_vec_supp_iff, not_not, not_not] at hnot
      have : y w = 0 := by
        dsimp [y]
        rw [hnot.1, hnot.2, mul_zero, mul_zero, sub_zero]
      exact hw this
    · intro hw_eq
      have : y w = 0 := by
        rw [hw_eq]
        dsimp [y]
        ring
      exact hw this

open Classical in
def op_979_csym_max_nullity_le_fort_transversal_number_ker_restrict
    {V : Type*} [Fintype V] [DecidableEq V] (A : Matrix V V ℝ) (T : Finset V) :
    A.mulVecLin.ker →ₗ[ℝ] (T → ℝ) where
  toFun x t := (x : V → ℝ) t.1
  map_add' x y := by ext; rfl
  map_smul' c x := by ext; rfl

open Classical in
lemma op_979_csym_max_nullity_le_fort_transversal_number_ker_restrict_injective
    {V : Type*} [Fintype V] [DecidableEq V] (A : Matrix V V ℝ) (T : Finset V)
    (hT : ∀ S ∈ op_979_csym_max_nullity_le_fort_transversal_number_kernel_supports A, (T ∩ S).Nonempty) :
    Function.Injective (op_979_csym_max_nullity_le_fort_transversal_number_ker_restrict A T) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  rintro ⟨x, hx_ker⟩ hx_in_ker
  rw [Subtype.ext_iff]
  dsimp
  by_contra hx_ne
  have hs_mem : op_979_csym_max_nullity_le_fort_transversal_number_vec_supp x ∈
      op_979_csym_max_nullity_le_fort_transversal_number_kernel_supports A := by
    rw [op_979_csym_max_nullity_le_fort_transversal_number_kernel_supports, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ⟨x, hx_ker, hx_ne, rfl⟩⟩
  have h_inter := hT (op_979_csym_max_nullity_le_fort_transversal_number_vec_supp x) hs_mem
  rcases h_inter with ⟨t, ht⟩
  rw [Finset.mem_inter] at ht
  have ht_zero : x t = 0 := by
    have := congr_fun (LinearMap.mem_ker.mp hx_in_ker) ⟨t, ht.1⟩
    exact this
  have ht_nonzero : x t ≠ 0 :=
    op_979_csym_max_nullity_le_fort_transversal_number_mem_vec_supp_iff.mp ht.2
  exact ht_nonzero ht_zero

open Classical in
lemma op_979_csym_max_nullity_le_fort_transversal_number_finrank_ker_le_card_of_transversal
    {V : Type*} [Fintype V] [DecidableEq V] (A : Matrix V V ℝ) (T : Finset V)
    (hT : ∀ S ∈ op_979_csym_max_nullity_le_fort_transversal_number_kernel_supports A, (T ∩ S).Nonempty) :
    Module.finrank ℝ A.mulVecLin.ker ≤ T.card := by
  have hinj := op_979_csym_max_nullity_le_fort_transversal_number_ker_restrict_injective A T hT
  have hle := LinearMap.finrank_le_finrank_of_injective hinj
  have hdim : Module.finrank ℝ (T → ℝ) = T.card := by
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_coe]
  rwa [hdim] at hle

open Classical in
lemma op_979_csym_max_nullity_le_fort_transversal_number_bdd_above_fort_transversal
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    BddAbove { k : ℕ | ∃ C : Finset (Finset V),
      (∀ F ∈ C, simple_graph_is_fort G (F : Set V)) ∧ is_compatible_collection C ∧ finset_transversal_number C = k } := by
  refine ⟨Fintype.card V, ?_⟩
  rintro k ⟨C, hC_fort, -, rfl⟩
  unfold finset_transversal_number
  have hmem : Fintype.card V ∈ { k : ℕ | ∃ T : Finset V, (∀ S ∈ C, (T ∩ S).Nonempty) ∧ T.card = k } := by
    refine ⟨Finset.univ, ?_, Finset.card_univ⟩
    intro S hS
    have hF := hC_fort S hS
    rcases hF.1 with ⟨v, hv⟩
    refine ⟨v, ?_⟩
    rw [Finset.mem_inter]
    exact ⟨Finset.mem_univ v, hv⟩
  exact Nat.sInf_le hmem

open Classical in
lemma op_979_csym_max_nullity_le_fort_transversal_number_finrank_ker_le_fort_transversal_number
    {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} (A : Matrix V V ℝ)
    (hA : is_csym_matrix G A) :
    Module.finrank ℝ A.mulVecLin.ker ≤ simple_graph_fort_transversal_number G := by
  let C := op_979_csym_max_nullity_le_fort_transversal_number_kernel_supports A
  have hC_fort : ∀ F ∈ C, simple_graph_is_fort G (F : Set V) := fun F hF =>
    op_979_csym_max_nullity_le_fort_transversal_number_kernel_supports_is_fort hA hF
  have hC_comp : is_compatible_collection C :=
    op_979_csym_max_nullity_le_fort_transversal_number_kernel_supports_compatible A
  have h_nonempty : { k : ℕ | ∃ T : Finset V, (∀ S ∈ C, (T ∩ S).Nonempty) ∧ T.card = k }.Nonempty := by
    refine ⟨Fintype.card V, Finset.univ, ?_, Finset.card_univ⟩
    intro S hS
    have hS_fort := hC_fort S hS
    rcases hS_fort.1 with ⟨v, hv⟩
    refine ⟨v, ?_⟩
    rw [Finset.mem_inter]
    exact ⟨Finset.mem_univ v, hv⟩
  have h_sinf_mem := Nat.sInf_mem h_nonempty
  rcases h_sinf_mem with ⟨T, hT_hit, hT_card⟩
  have h_le_card : Module.finrank ℝ A.mulVecLin.ker ≤ T.card :=
    op_979_csym_max_nullity_le_fort_transversal_number_finrank_ker_le_card_of_transversal A T hT_hit
  have h_trans_mem : finset_transversal_number C ∈
      { k : ℕ | ∃ C' : Finset (Finset V),
        (∀ F ∈ C', simple_graph_is_fort G (F : Set V)) ∧ is_compatible_collection C' ∧ finset_transversal_number C' = k } :=
    ⟨C, hC_fort, hC_comp, rfl⟩
  have hbdd := op_979_csym_max_nullity_le_fort_transversal_number_bdd_above_fort_transversal G
  have h_trans_le : finset_transversal_number C ≤ simple_graph_fort_transversal_number G :=
    le_csSup hbdd h_trans_mem
  have h_le_trans : Module.finrank ℝ A.mulVecLin.ker ≤ finset_transversal_number C := by
    change Module.finrank ℝ A.mulVecLin.ker ≤ sInf { k : ℕ | ∃ T : Finset V, (∀ S ∈ C, (T ∩ S).Nonempty) ∧ T.card = k }
    rw [← hT_card]
    exact h_le_card
  exact le_trans h_le_trans h_trans_le

/-- Theorem 2.10: For every finite simple graph G, N(G) ≤ T(G). -/
theorem op_979_csym_max_nullity_le_fort_transversal_number
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) :
    simple_graph_csym_max_nullity G ≤ simple_graph_fort_transversal_number G := by
  classical
  unfold simple_graph_csym_max_nullity
  cases { k : ℕ | ∃ A : Matrix V V ℝ, is_csym_matrix G A ∧ Module.finrank ℝ A.mulVecLin.ker = k }.eq_empty_or_nonempty with
  | inl he =>
    rw [he, csSup_empty]
    exact bot_le
  | inr hne =>
    apply csSup_le hne
    rintro k ⟨A, hA, rfl⟩
    exact op_979_csym_max_nullity_le_fort_transversal_number_finrank_ker_le_fort_transversal_number A hA
