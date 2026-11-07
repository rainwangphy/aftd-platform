import AFTD.Prelude
import AFTD.Kb.Tcs.PetrialLogConcave
import AFTD.Kb.Tcs.PetrialCoeff
import AFTD.Kb.Physics.InstDecidableRelPathGraph
import AFTD.Kb.Tcs.PetrialMatrix

/-!
# op_1239_path_graph_petrial_log_concave

Topic: combinatorics   Node: a5e37ea27b02

Provenance: formalization of a published result. Source: arXiv:2611.07503, Section 6

For every n : ℕ, the path graph pathGraph n has a log-concave partial Petrial polynomial (petrial_log_concave (SimpleGraph.pathGraph n)).
-/

set_option linter.unusedSimpArgs false in
private lemma op_1239_path_graph_petrial_log_concave_rec_i {n : ℕ} (F : Finset (Fin n)) (z : Fin n → ZMod 2)
    (hz : ∀ i, (petrial_matrix (SimpleGraph.pathGraph n) F).mulVec z i = 0)
    (i : Fin n) (hi : i.val + 1 < n) :
    z ⟨i.val + 1, hi⟩ + (if h : i.val = 0 then 0 else z ⟨i.val - 1, by omega⟩)
      + (if i ∈ F then (1:ZMod 2) else 0) * z i = 0 := by
  classical
  have hmain := hz i
  rw [petrial_matrix, Matrix.add_mulVec, Pi.add_apply] at hmain
  rw [SimpleGraph.adjMatrix_mulVec_apply, Matrix.mulVec_diagonal] at hmain
  have hsum : ∑ u ∈ (SimpleGraph.pathGraph n).neighborFinset i, z u =
      z ⟨i.val + 1, hi⟩ + (if h : i.val = 0 then 0 else z ⟨i.val - 1, by omega⟩) := by
    have hset : (SimpleGraph.pathGraph n).neighborFinset i
        = ({⟨i.val + 1, hi⟩} : Finset (Fin n)) ∪ (if h : i.val = 0 then ∅ else {⟨i.val - 1, by omega⟩}) := by
      ext u
      rw [SimpleGraph.mem_neighborFinset, SimpleGraph.pathGraph_adj]
      simp only [Finset.mem_union, Finset.mem_singleton]
      constructor
      · rintro (h | h)
        · left; apply Fin.ext; simp only [Fin.val_mk]; omega
        · right
          have hiz : ¬ (i.val = 0) := by omega
          simp only [dif_neg hiz, Finset.mem_singleton]
          apply Fin.ext; simp only [Fin.val_mk]; omega
      · rintro (h | h)
        · left; rw [h]
        · split_ifs at h with h0
          · simp at h
          · right
            rw [Finset.mem_singleton] at h
            rw [h]; simp only [Fin.val_mk]; omega
    rw [hset, Finset.sum_union]
    · rw [Finset.sum_singleton]
      split_ifs with h0
      · simp
      · rw [Finset.sum_singleton]
    · refine Finset.disjoint_left.mpr ?_
      intro a ha ha'
      simp only [Finset.mem_singleton] at ha
      subst ha
      split_ifs at ha' with h0
      · simp at ha'
      · simp only [Finset.mem_singleton, Fin.ext_iff] at ha'
        omega
  rw [← hsum]
  exact hmain

set_option linter.unusedSimpArgs false in
private lemma op_1239_path_graph_petrial_log_concave_kernel_zero {n : ℕ} (F : Finset (Fin n)) (z : Fin n → ZMod 2)
    (hz : ∀ i, (petrial_matrix (SimpleGraph.pathGraph n) F).mulVec z i = 0)
    (hn : 0 < n) (hz0 : z ⟨0, hn⟩ = 0) : z = 0 := by
  classical
  funext j
  have key : ∀ (k : ℕ) (hk : k < n), z ⟨k, hk⟩ = 0 := by
    intro k
    refine Nat.strong_induction_on k (fun k ih => ?_)
    intro hk
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      exact hz0
    · obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
      have hk' : k' < n := by omega
      have hi : k' + 1 < n := hk
      have hrec := op_1239_path_graph_petrial_log_concave_rec_i F z hz ⟨k', hk'⟩ hi
      have hz1 : z ⟨k', hk'⟩ = 0 := ih k' (by omega) hk'
      have hz2 : (if h : k' = 0 then (0:ZMod 2) else z ⟨k' - 1, by omega⟩) = 0 := by
        split_ifs with h0
        · rfl
        · exact ih (k' - 1) (by omega) (by omega)
      have hz3 : z ⟨k' + 1, hi⟩ = z ⟨k' + 1, hk⟩ := by congr 1
      rw [hz2, hz1, mul_zero, add_zero, add_zero] at hrec
      rw [← hz3]
      exact hrec
  exact key j.val j.isLt

set_option linter.unusedSimpArgs false in
private lemma op_1239_path_graph_petrial_log_concave_kernel_finrank {n : ℕ} (F : Finset (Fin n)) (hn : 0 < n) :
    Module.finrank (ZMod 2) (petrial_matrix (SimpleGraph.pathGraph n) F).mulVecLin.ker ≤ 1 := by
  classical
  let M := petrial_matrix (SimpleGraph.pathGraph n) F
  change Module.finrank (ZMod 2) M.mulVecLin.ker ≤ 1
  let e : (Fin n → ZMod 2) →ₗ[ZMod 2] ZMod 2 := LinearMap.proj (φ := fun _ : Fin n => ZMod 2) ⟨0, hn⟩
  let φ : M.mulVecLin.ker →ₗ[ZMod 2] ZMod 2 := e.comp (Submodule.subtype M.mulVecLin.ker)
  have hinj : Function.Injective φ := by
    intro x y hxy
    have hxy' : x.val ⟨0, hn⟩ = y.val ⟨0, hn⟩ := hxy
    apply Subtype.ext
    have hmem0 : M.mulVec (x.val - y.val) = 0 := by
      have h1 := (LinearMap.mem_ker).mp (x - y).2
      have h2 : M.mulVecLin ((x : Fin n → ZMod 2) - (y : Fin n → ZMod 2)) = 0 := by
        rwa [Submodule.coe_sub] at h1
      simpa only [Matrix.mulVecLin_apply] using h2
    have hz0 : (x.val - y.val) ⟨0, hn⟩ = 0 := by
      rw [Pi.sub_apply, hxy', sub_self]
    have hfinal := op_1239_path_graph_petrial_log_concave_kernel_zero F (x.val - y.val) (fun i => by rw [hmem0]; rfl) hn hz0
    exact sub_eq_zero.mp hfinal
  have hle := LinearMap.finrank_le_finrank_of_injective (f := φ) hinj
  rwa [Module.finrank_self] at hle

set_option linter.unusedSimpArgs false in
private lemma op_1239_path_graph_petrial_log_concave_rank_ge (n : ℕ) (F : Finset (Fin n)) :
    n - 1 ≤ (petrial_matrix (SimpleGraph.pathGraph n) F).rank := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  · set M := petrial_matrix (SimpleGraph.pathGraph n) F
    have hker : Module.finrank (ZMod 2) M.mulVecLin.ker ≤ 1 :=
      op_1239_path_graph_petrial_log_concave_kernel_finrank F h
    have hM := LinearMap.finrank_range_add_finrank_ker M.mulVecLin
    have hfin : Module.finrank (ZMod 2) (Fin n → ZMod 2) = n := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
    rw [hfin] at hM
    have hrank : M.rank = Module.finrank (ZMod 2) M.mulVecLin.range := rfl
    have hgoal : n - 1 ≤ Module.finrank (ZMod 2) M.mulVecLin.range := by omega
    rwa [hrank]

private lemma op_1239_path_graph_petrial_log_concave_rank_le (n : ℕ) (F : Finset (Fin n)) :
    (petrial_matrix (SimpleGraph.pathGraph n) F).rank ≤ n := by
  have h := Matrix.rank_le_card_height (petrial_matrix (SimpleGraph.pathGraph n) F)
  simpa using h

/-- Path graphs have log-concave partial Petrial polynomials. -/
theorem op_1239_path_graph_petrial_log_concave (n : ℕ) :
    petrial_log_concave (SimpleGraph.pathGraph n) := by
  intro k hi hj
  obtain ⟨i, hik, hic⟩ := hi
  obtain ⟨j, hkj, hjc⟩ := hj
  have hni : n - 1 ≤ i := by
    obtain ⟨F, hF⟩ := Finset.card_ne_zero.mp hic
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hF
    rw [← hF]
    exact op_1239_path_graph_petrial_log_concave_rank_ge n F
  have hnj : j ≤ n := by
    obtain ⟨F, hF⟩ := Finset.card_ne_zero.mp hjc
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hF
    rw [← hF]
    exact op_1239_path_graph_petrial_log_concave_rank_le n F
  exfalso
  omega
