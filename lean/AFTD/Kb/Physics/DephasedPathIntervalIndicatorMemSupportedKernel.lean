import AFTD.Prelude
import AFTD.Kb.Physics.DephasedSupportedKernel
import AFTD.Kb.Physics.DephasedPathIntervalBlock
import AFTD.Kb.Physics.InstDecidableRelPathGraph
import AFTD.Kb.Physics.TreeSubmatrixKer

/-!
# dephased_path_interval_indicator_mem_supported_kernel

Topic: quantum_mechanics   Node: 7904cd9412da

Provenance: helper lemma. OP-827, path interval expansion for supported cut kernels

An alternating interval contained in a path subsystem has its indicator in the supported cut kernel exactly when all its selected weights are nonzero and both existing adjacent boundary vertices are in the subsystem.
-/

theorem dephased_path_interval_indicator_mem_supported_kernel_mem_tree_submatrix_ker_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (S : Finset V)
    (x : ↥S → ZMod 2) :
    x ∈ tree_submatrix_ker G S ↔
      ∀ r : V, r ∉ S → (∑ c : ↥S, (if G.Adj r c.1 then (1 : ZMod 2) else 0) * x c) = 0 := by
  dsimp [tree_submatrix_ker]
  rw [LinearMap.mem_ker]
  constructor
  · intro h r hr
    have h1 := congr_fun h ⟨r, by simpa using hr⟩
    simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Matrix.submatrix_apply,
      Pi.zero_apply] at h1
    simp_rw [SimpleGraph.adjMatrix_apply] at h1
    exact h1
  · intro h
    ext ⟨r, hr⟩
    simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Matrix.submatrix_apply,
      Pi.zero_apply]
    simp_rw [SimpleGraph.adjMatrix_apply]
    have hr' : r ∉ S := by simpa using hr
    exact h r hr'

theorem dephased_path_interval_indicator_mem_supported_kernel_mem_dephased_supported_kernel_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (q : V → ℝ) (S : Finset V)
    (x : ↥S → ZMod 2) :
    x ∈ dephased_supported_kernel G q S ↔
      (∀ r : V, r ∉ S → (∑ c : ↥S, (if G.Adj r c.1 then (1 : ZMod 2) else 0) * x c) = 0) ∧
      (∀ i : ↥S, q i.1 = 0 → x i = 0) := by
  dsimp [dephased_supported_kernel]
  rw [Submodule.mem_inf]
  rw [dephased_path_interval_indicator_mem_supported_kernel_mem_tree_submatrix_ker_iff]
  rfl

lemma dephased_path_interval_indicator_mem_supported_kernel_mem_filter_iff
    (n : ℕ) (a b r v : Fin n) :
    v ∈ (dephased_path_interval_block n a b).filter ((SimpleGraph.pathGraph n).Adj r) ↔
      a.val ≤ v.val ∧ v.val ≤ b.val ∧ v.val % 2 = a.val % 2 ∧
      (r.val + 1 = v.val ∨ v.val + 1 = r.val) := by
  simp only [Finset.mem_filter, dephased_path_interval_block, Finset.mem_univ, true_and,
    SimpleGraph.pathGraph_adj]
  tauto

lemma dephased_path_interval_indicator_mem_supported_kernel_filter_eq_singleton_left
    (n : ℕ) (a b r : Fin n)
    (hab : a.val ≤ b.val) (hr : r.val + 1 = a.val) :
    (dephased_path_interval_block n a b).filter ((SimpleGraph.pathGraph n).Adj r) = {a} := by
  ext v
  rw [dephased_path_interval_indicator_mem_supported_kernel_mem_filter_iff, Finset.mem_singleton]
  constructor
  · rintro ⟨ha, hb, hpar, hadj⟩
    ext
    rcases hadj with h1 | h2 <;> omega
  · rintro rfl
    refine ⟨le_rfl, hab, rfl, Or.inl hr⟩

lemma dephased_path_interval_indicator_mem_supported_kernel_filter_eq_singleton_right
    (n : ℕ) (a b r : Fin n)
    (hab : a.val ≤ b.val) (hpar : a.val % 2 = b.val % 2) (hr : b.val + 1 = r.val) :
    (dephased_path_interval_block n a b).filter ((SimpleGraph.pathGraph n).Adj r) = {b} := by
  ext v
  rw [dephased_path_interval_indicator_mem_supported_kernel_mem_filter_iff, Finset.mem_singleton]
  constructor
  · rintro ⟨ha, hb, hp, hadj⟩
    ext
    rcases hadj with h1 | h2 <;> omega
  · rintro rfl
    refine ⟨hab, le_rfl, hpar.symm, Or.inr hr⟩

lemma dephased_path_interval_indicator_mem_supported_kernel_filter_eq_pair
    (n : ℕ) (a b r : Fin n)
    (hodd : (r.val + 1) % 2 = a.val % 2)
    (ha : a.val < r.val) (hb : r.val < b.val) :
    ∃ v1 v2 : Fin n, v1 ≠ v2 ∧
      (dephased_path_interval_block n a b).filter ((SimpleGraph.pathGraph n).Adj r) = {v1, v2} := by
  have h1 : r.val - 1 < n := by omega
  have h2 : r.val + 1 < n := by omega
  let v1 : Fin n := ⟨r.val - 1, h1⟩
  let v2 : Fin n := ⟨r.val + 1, h2⟩
  use v1, v2
  have hne : v1 ≠ v2 := by
    intro h
    apply_fun Fin.val at h
    dsimp [v1, v2] at h
    omega
  refine ⟨hne, ?_⟩
  ext v
  rw [dephased_path_interval_indicator_mem_supported_kernel_mem_filter_iff, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hva, hvb, hvp, hadj⟩
    rcases hadj with h_adj1 | h_adj2
    · right; apply Fin.ext; dsimp [v2]; omega
    · left; apply Fin.ext; dsimp [v1]; omega
  · rintro (rfl | rfl)
    · dsimp [v1]; refine ⟨by omega, by omega, by omega, Or.inr (by omega)⟩
    · dsimp [v2]; refine ⟨by omega, by omega, by omega, Or.inl (by omega)⟩

lemma dephased_path_interval_indicator_mem_supported_kernel_filter_eq_empty_of_even
    (n : ℕ) (a b r : Fin n)
    (heven : r.val % 2 = a.val % 2) :
    (dephased_path_interval_block n a b).filter ((SimpleGraph.pathGraph n).Adj r) = ∅ := by
  ext v
  rw [dephased_path_interval_indicator_mem_supported_kernel_mem_filter_iff]
  constructor
  · rintro ⟨-, -, hpar, hadj⟩
    rcases hadj with h1 | h2 <;> omega
  · intro h; cases h

lemma dephased_path_interval_indicator_mem_supported_kernel_filter_eq_empty_of_lt
    (n : ℕ) (a b r : Fin n)
    (hlt : r.val + 1 < a.val) :
    (dephased_path_interval_block n a b).filter ((SimpleGraph.pathGraph n).Adj r) = ∅ := by
  ext v
  rw [dephased_path_interval_indicator_mem_supported_kernel_mem_filter_iff]
  constructor
  · rintro ⟨ha, -, -, hadj⟩
    rcases hadj with h1 | h2 <;> omega
  · intro h; cases h

lemma dephased_path_interval_indicator_mem_supported_kernel_filter_eq_empty_of_gt
    (n : ℕ) (a b r : Fin n)
    (hgt : b.val + 1 < r.val) :
    (dephased_path_interval_block n a b).filter ((SimpleGraph.pathGraph n).Adj r) = ∅ := by
  ext v
  rw [dephased_path_interval_indicator_mem_supported_kernel_mem_filter_iff]
  constructor
  · rintro ⟨-, hb, -, hadj⟩
    rcases hadj with h1 | h2 <;> omega
  · intro h; cases h

lemma dephased_path_interval_indicator_mem_supported_kernel_card_filter_eq_zero_iff
    (n : ℕ) (a b r : Fin n)
    (hab : a.val ≤ b.val) (hpar : a.val % 2 = b.val % 2) :
    ((((dephased_path_interval_block n a b).filter ((SimpleGraph.pathGraph n).Adj r)).card : ZMod 2) = 0) ↔
      ¬ (r.val + 1 = a.val ∨ b.val + 1 = r.val) := by
  constructor
  · intro h0 h_adj
    rcases h_adj with h_left | h_right
    · rw [dephased_path_interval_indicator_mem_supported_kernel_filter_eq_singleton_left n a b r hab h_left] at h0
      simp at h0
    · rw [dephased_path_interval_indicator_mem_supported_kernel_filter_eq_singleton_right n a b r hab hpar h_right] at h0
      simp at h0
  · intro hnot
    have hnot1 : r.val + 1 ≠ a.val := fun h => hnot (Or.inl h)
    have hnot2 : b.val + 1 ≠ r.val := fun h => hnot (Or.inr h)
    by_cases heven : r.val % 2 = a.val % 2
    · rw [dephased_path_interval_indicator_mem_supported_kernel_filter_eq_empty_of_even n a b r heven]
      simp
    · have hodd : (r.val + 1) % 2 = a.val % 2 := by omega
      have hcases : r.val + 1 < a.val ∨ b.val + 1 < r.val ∨ (a.val < r.val ∧ r.val < b.val) := by omega
      rcases hcases with hlt | hgt | ⟨ha, hb⟩
      · rw [dephased_path_interval_indicator_mem_supported_kernel_filter_eq_empty_of_lt n a b r hlt]
        simp
      · rw [dephased_path_interval_indicator_mem_supported_kernel_filter_eq_empty_of_gt n a b r hgt]
        simp
      · rcases dephased_path_interval_indicator_mem_supported_kernel_filter_eq_pair n a b r hodd ha hb with ⟨v1, v2, hne, hset⟩
        rw [hset]
        rw [Finset.card_insert_of_notMem (by simp [hne])]
        rw [Finset.card_singleton]
        rfl

theorem dephased_path_interval_indicator_mem_supported_kernel_sum_indicator_adj
    (n : ℕ) (a b : Fin n) (S : Finset (Fin n))
    (hsub : dephased_path_interval_block n a b ⊆ S) (r : Fin n) :
    (∑ c : ↥S, (if (SimpleGraph.pathGraph n).Adj r c.1 then (1 : ZMod 2) else 0) *
      (if c.1 ∈ dephased_path_interval_block n a b then 1 else 0)) =
    ((((dephased_path_interval_block n a b).filter ((SimpleGraph.pathGraph n).Adj r)).card : ZMod 2)) := by
  let I := dephased_path_interval_block n a b
  let f : Fin n → ZMod 2 := fun v => (if (SimpleGraph.pathGraph n).Adj r v then 1 else 0) * (if v ∈ I then 1 else 0)
  change (∑ c : ↥S, f c.1) = _
  rw [Finset.sum_coe_sort]
  have hf : ∀ v, f v = if v ∈ I ∧ (SimpleGraph.pathGraph n).Adj r v then 1 else 0 := by
    intro v
    dsimp [f]
    split_ifs <;> aesop
  simp_rw [hf]
  rw [← Finset.sum_filter]
  have h_subset : (S.filter (fun v => v ∈ I ∧ (SimpleGraph.pathGraph n).Adj r v)) =
      I.filter ((SimpleGraph.pathGraph n).Adj r) := by
    ext v
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨hvS, hvI, hadj⟩
      exact ⟨hvI, hadj⟩
    · rintro ⟨hvI, hadj⟩
      exact ⟨hsub hvI, hvI, hadj⟩
  rw [h_subset]
  simp [I]

open scoped Classical in
theorem dephased_path_interval_indicator_mem_supported_kernel
    (n : ℕ) (q : Fin n → ℝ) (S : Finset (Fin n)) (a b : Fin n)
    (hab : a.val ≤ b.val) (hpar : a.val % 2 = b.val % 2)
    (hsub : dephased_path_interval_block n a b ⊆ S) :
    (fun i : ↥S => if i.1 ∈ dephased_path_interval_block n a b then (1 : ZMod 2) else 0) ∈
      dephased_supported_kernel (SimpleGraph.pathGraph n) q S ↔
    (∀ i ∈ dephased_path_interval_block n a b, q i ≠ 0) ∧
      (∀ k : Fin n, k.val + 1 = a.val ∨ b.val + 1 = k.val → k ∈ S) := by
  rw [dephased_path_interval_indicator_mem_supported_kernel_mem_dephased_supported_kernel_iff]
  have hsum : (∀ r : Fin n, r ∉ S → (∑ c : ↥S, (if (SimpleGraph.pathGraph n).Adj r c.1 then (1 : ZMod 2) else 0) *
      (if c.1 ∈ dephased_path_interval_block n a b then 1 else 0)) = 0) ↔
      (∀ k : Fin n, k.val + 1 = a.val ∨ b.val + 1 = k.val → k ∈ S) := by
    simp_rw [dephased_path_interval_indicator_mem_supported_kernel_sum_indicator_adj n a b S hsub]
    simp_rw [dephased_path_interval_indicator_mem_supported_kernel_card_filter_eq_zero_iff n a b _ hab hpar]
    constructor
    · intro h k hk
      by_contra hkS
      exact (h k hkS) hk
    · intro h r hr h_adj
      exact hr (h r h_adj)
  have hzero : (∀ i : ↥S, q i.1 = 0 → (if i.1 ∈ dephased_path_interval_block n a b then (1 : ZMod 2) else 0) = 0) ↔
      (∀ i ∈ dephased_path_interval_block n a b, q i ≠ 0) := by
    constructor
    · intro h i hi hqi
      have hiS : i ∈ S := hsub hi
      have h1 := h ⟨i, hiS⟩ hqi
      simp only [hi, if_true] at h1
      revert h1; decide
    · intro h i hqi
      split_ifs with hi
      · exact False.elim (h i.1 hi hqi)
      · rfl
  rw [hsum, hzero]
  tauto
