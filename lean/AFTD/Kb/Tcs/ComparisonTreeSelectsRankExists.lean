import AFTD.Prelude
import AFTD.Kb.Tcs.ComparisonTreeSelectsRank
import AFTD.Kb.Tcs.ComparisonTreeEval
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Tcs.ComparisonTree
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# comparison_tree_selects_rank_exists

Topic: algorithms   Node: 0e340a839912

Provenance: helper lemma. step towards v_selection_16_8_lower_bound

For every n and every rank r : Fin n there exists a comparison decision tree on n elements that correctly selects the element of rank r.
-/

def comparison_tree_selects_rank_exists_all_pairs_list (n : ℕ) : List (Fin n × Fin n) :=
  (List.finRange n).product (List.finRange n)

lemma comparison_tree_selects_rank_exists_mem_all_pairs_list {n : ℕ} (p : Fin n × Fin n) :
    p ∈ comparison_tree_selects_rank_exists_all_pairs_list n := by
  rcases p with ⟨i, j⟩
  simp [comparison_tree_selects_rank_exists_all_pairs_list]

def comparison_tree_selects_rank_exists_update_matrix {n : ℕ} (M : Fin n → Fin n → Bool) (i j : Fin n) (b : Bool) :
    Fin n → Fin n → Bool :=
  fun x y => if x = i ∧ y = j then b else M x y

def comparison_tree_selects_rank_exists_build {n : ℕ} (choose : (Fin n → Fin n → Bool) → Fin n) :
    List (Fin n × Fin n) → (Fin n → Fin n → Bool) → ComparisonTree n
  | [], M => ComparisonTree.leaf (choose M)
  | (i, j) :: rest, M =>
    ComparisonTree.branch i j
      (comparison_tree_selects_rank_exists_build choose rest (comparison_tree_selects_rank_exists_update_matrix M i j true))
      (comparison_tree_selects_rank_exists_build choose rest (comparison_tree_selects_rank_exists_update_matrix M i j false))

theorem comparison_tree_selects_rank_exists_build_eval {n : ℕ} {α : Type*} [LinearOrder α] (v : Fin n → α)
    (choose : (Fin n → Fin n → Bool) → Fin n)
    (L : List (Fin n × Fin n)) (M : Fin n → Fin n → Bool) :
    comparison_tree_eval v (comparison_tree_selects_rank_exists_build choose L M) =
      choose (L.foldl (fun m p => comparison_tree_selects_rank_exists_update_matrix m p.1 p.2 (decide (v p.1 < v p.2))) M) := by
  induction L generalizing M with
  | nil =>
    simp [comparison_tree_selects_rank_exists_build, comparison_tree_eval]
  | cons head tail ih =>
    rcases head with ⟨i, j⟩
    simp [comparison_tree_selects_rank_exists_build, comparison_tree_eval]
    split_ifs with h
    · rw [ih]
      have : decide (v i < v j) = true := by simp [h]
      rw [this]
    · rw [ih]
      have : decide (v i < v j) = false := by simp [h]
      rw [this]

lemma comparison_tree_selects_rank_exists_foldl_update_matrix {n : ℕ} {α : Type*} [LinearOrder α] (v : Fin n → α)
    (L : List (Fin n × Fin n)) (M : Fin n → Fin n → Bool) (i j : Fin n) :
    (L.foldl (fun m p => comparison_tree_selects_rank_exists_update_matrix m p.1 p.2 (decide (v p.1 < v p.2))) M) i j =
      if (i, j) ∈ L then decide (v i < v j) else M i j := by
  induction L generalizing M with
  | nil => simp
  | cons head tail ih =>
    rcases head with ⟨x, y⟩
    simp only [List.foldl_cons, ih, List.mem_cons]
    by_cases h : (i, j) ∈ tail
    · simp [h]
    · simp [h]
      dsimp [comparison_tree_selects_rank_exists_update_matrix]
      split_ifs with h2
      · rcases h2 with ⟨rfl, rfl⟩
        simp
      · simp

lemma comparison_tree_selects_rank_exists_foldl_update_matrix_all {n : ℕ} {α : Type*} [LinearOrder α] (v : Fin n → α)
    (L : List (Fin n × Fin n)) (hL : ∀ p, p ∈ L) (M : Fin n → Fin n → Bool) :
    (L.foldl (fun m p => comparison_tree_selects_rank_exists_update_matrix m p.1 p.2 (decide (v p.1 < v p.2))) M) =
      fun i j => decide (v i < v j) := by
  ext i j
  rw [comparison_tree_selects_rank_exists_foldl_update_matrix]
  simp [hL (i, j)]

def comparison_tree_selects_rank_exists_count_smaller {n : ℕ} (M : Fin n → Fin n → Bool) (a : Fin n) : ℕ :=
  (Finset.filter (fun b => M b a = true) Finset.univ).card

lemma comparison_tree_selects_rank_exists_card_filter_perm_lt {n : ℕ} (σ : Equiv.Perm (Fin n)) (a : Fin n) :
    (Finset.filter (fun b => σ b < σ a) Finset.univ).card = (σ a).val := by
  have h1 : Finset.filter (fun b => σ b < σ a) Finset.univ =
      (Finset.Iio (σ a)).map σ.symm.toEmbedding := by
    ext x
    simp
  rw [h1, Finset.card_map, Fin.card_Iio]

lemma comparison_tree_selects_rank_exists_count_smaller_perm {n : ℕ} (σ : Equiv.Perm (Fin n)) (a : Fin n) :
    comparison_tree_selects_rank_exists_count_smaller (fun b a => decide (σ b < σ a)) a = (σ a).val := by
  dsimp [comparison_tree_selects_rank_exists_count_smaller]
  have h : (Finset.filter (fun b => decide (σ b < σ a) = true) Finset.univ) =
      (Finset.filter (fun b => σ b < σ a) Finset.univ) := by
    ext b
    simp
  rw [h]
  exact comparison_tree_selects_rank_exists_card_filter_perm_lt σ a

noncomputable def comparison_tree_selects_rank_exists_choose_rank {n : ℕ} (r : Fin n) (M : Fin n → Fin n → Bool) : Fin n :=
  if h : ∃ a : Fin n, comparison_tree_selects_rank_exists_count_smaller M a = r.val then Classical.choose h else r

lemma comparison_tree_selects_rank_exists_choose_rank_spec {n : ℕ} (r : Fin n) (σ : Equiv.Perm (Fin n)) :
    σ (comparison_tree_selects_rank_exists_choose_rank r (fun b a => decide (σ b < σ a))) = r := by
  dsimp [comparison_tree_selects_rank_exists_choose_rank]
  have h : ∃ a : Fin n, comparison_tree_selects_rank_exists_count_smaller (fun b a => decide (σ b < σ a)) a = r.val := by
    use σ.symm r
    rw [comparison_tree_selects_rank_exists_count_smaller_perm]
    simp
  rw [dif_pos h]
  have ha : comparison_tree_selects_rank_exists_count_smaller (fun b a => decide (σ b < σ a)) (Classical.choose h) = r.val :=
    Classical.choose_spec h
  rw [comparison_tree_selects_rank_exists_count_smaller_perm] at ha
  exact Fin.ext ha

/-- Every rank-selection problem is solvable by some comparison decision tree, so the set of depths used in `comparison_selection_complexity` is nonempty. -/
theorem comparison_tree_selects_rank_exists {n : ℕ} (r : Fin n) : ∃ T : ComparisonTree n, comparison_tree_selects_rank T r := by
  let choose := comparison_tree_selects_rank_exists_choose_rank r
  let T := comparison_tree_selects_rank_exists_build choose (comparison_tree_selects_rank_exists_all_pairs_list n) (fun _ _ => false)
  use T
  intro σ
  dsimp [T, choose]
  rw [comparison_tree_selects_rank_exists_build_eval]
  rw [comparison_tree_selects_rank_exists_foldl_update_matrix_all (⇑σ) (comparison_tree_selects_rank_exists_all_pairs_list n)
    comparison_tree_selects_rank_exists_mem_all_pairs_list]
  exact comparison_tree_selects_rank_exists_choose_rank_spec r σ
