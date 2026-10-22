import AFTD.Prelude
import AFTD.Kb.Tcs.IsKDiagonalOn
import AFTD.Kb.Tcs.ExistsNontrivialSolutionOfCardGt

/-!
# common_space_diagonal_tensor_rank_bound

Topic: combinatorics   Node: 59e5f3cc552e

Provenance: formalization of a published result. Source: arXiv:2610.26686 Lemma 3

Common-Space Diagonal Tensor Rank Bound (arXiv:2610.26686, Lemma 3). Let k = n + 1 ≥ 2 (with 1 ≤ n), and let V ⊆ U be a finite set. Let f : (Fin (n + 1) → U) → ℚ be (n + 1)-diagonal on V, meaning that for all x : Fin (n + 1) → U taking values in V, f(x) ≠ 0 if and only if all entries of x are equal. Suppose there exist functions p : Fin d → (U → ℚ) and G : Fin (n + 1) → Fin d → (Fin n → U) → ℚ such that for all x : Fin (n + 1) → U, f(x) = ∑_{i ≠ 0} ∑_{j} p_j(x_i) G_{i,j}(x ∘ i.succAbove), where the outer sum is over nonzero indices i ∈ Fin (n + 1) and x ∘ i.succAbove is the tuple obtained by omitting the i-th entry. Then the cardinality of V is at most d.
-/

open Classical in
theorem common_space_diagonal_tensor_rank_bound_term_sum_zero {U : Type*} (n d : ℕ) {V : Finset U} (a : V) (h : V → ℚ)
    (p : Fin d → U → ℚ)
    (h_ortho : ∀ j : Fin d, ∑ x : V, h x * p j x = 0)
    (G : Fin (n + 1) → Fin d → (Fin n → U) → ℚ)
    (i : Fin (n + 1)) (hi : i ≠ 0) (j : Fin d) :
    let w : Fin (n + 1) → V → ℚ := Fin.cons (fun u => if u = a then (1:ℚ) else 0) (fun _ => h)
    ∑ x : Fin (n + 1) → V, (∏ t : Fin (n + 1), w t (x t)) * (p j (x i) * G i j ((fun m => (x m : U)) ∘ i.succAbove)) = 0 := by
  intro w
  have hequiv := (Fin.insertNthEquiv (fun _ => V) i).sum_comp
    (fun x => (∏ t : Fin (n + 1), w t (x t)) * (p j (x i) * G i j ((fun m => (x m : U)) ∘ i.succAbove)))
  rw [← hequiv]
  rw [Fintype.sum_prod_type]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro z _
  change ∑ u : V, (∏ t : Fin (n + 1), w t (Fin.insertNth (α := fun _ => V) i u z t)) *
    (p j ((Fin.insertNth (α := fun _ => V) i u z i : U)) *
      G i j ((fun m => (Fin.insertNth (α := fun _ => V) i u z m : U)) ∘ i.succAbove)) = 0
  have hprod : ∀ u : V, ∏ t : Fin (n + 1), w t (Fin.insertNth (α := fun _ => V) i u z t) =
      h u * ∏ m : Fin n, w (i.succAbove m) (z m) := by
    intro u
    rw [Fin.prod_univ_succAbove (fun t => w t (Fin.insertNth (α := fun _ => V) i u z t)) i]
    rw [Fin.insertNth_apply_same]
    have hw : w i = h := by
      have hi' : (i.pred hi).succ = i := Fin.succ_pred i hi
      rw [← hi']
      exact Fin.cons_succ (α := fun _ => V → ℚ) _ _ (i.pred hi)
    rw [hw]
    congr 1
    apply Finset.prod_congr rfl
    intro m _
    rw [Fin.insertNth_apply_succAbove]
  have hcomp_u : ∀ u : V, ((fun m => (Fin.insertNth (α := fun _ => V) i u z m : U)) ∘ i.succAbove) = fun m => (z m : U) := by
    intro u
    ext m
    simp only [Function.comp_apply]
    congr 1
    exact Fin.insertNth_apply_succAbove (α := fun _ => V) i u z m
  have hsame : ∀ u : V, (Fin.insertNth (α := fun _ => V) i u z i : U) = (u : U) := by
    intro u
    congr 1
    exact Fin.insertNth_apply_same (α := fun _ => V) i u z
  have hstep : (∑ u : V, (∏ t : Fin (n + 1), w t (Fin.insertNth (α := fun _ => V) i u z t)) *
      (p j ((Fin.insertNth (α := fun _ => V) i u z i : U)) *
        G i j ((fun m => (Fin.insertNth (α := fun _ => V) i u z m : U)) ∘ i.succAbove))) =
    ∑ u : V, (h u * p j (u : U)) * ((∏ m : Fin n, w (i.succAbove m) (z m)) * G i j (fun m => (z m : U))) := by
    apply Finset.sum_congr rfl
    intro u _
    rw [hprod u, hsame u, hcomp_u u]
    ring
  rw [hstep, ← Finset.sum_mul, h_ortho j, zero_mul]

open Classical in
theorem common_space_diagonal_tensor_rank_bound_total_sum_zero {U : Type*} (n d : ℕ) {V : Finset U} (a : V) (h : V → ℚ)
    (f : (Fin (n + 1) → U) → ℚ)
    (p : Fin d → U → ℚ)
    (h_ortho : ∀ j : Fin d, ∑ x : V, h x * p j x = 0)
    (G : Fin (n + 1) → Fin d → (Fin n → U) → ℚ)
    (hdecomp : ∀ x : Fin (n + 1) → U,
      f x = ∑ i ∈ Finset.univ.filter (· ≠ (0 : Fin (n + 1))),
        ∑ j : Fin d, p j (x i) * G i j (x ∘ i.succAbove)) :
    let w : Fin (n + 1) → V → ℚ := Fin.cons (fun u => if u = a then (1:ℚ) else 0) (fun _ => h)
    ∑ x : Fin (n + 1) → V, (∏ t : Fin (n + 1), w t (x t)) * f (fun m => (x m : U)) = 0 := by
  intro w
  have hrew : (fun x : Fin (n + 1) → V => (∏ t : Fin (n + 1), w t (x t)) * f (fun m => (x m : U))) =
    fun x => ∑ i ∈ Finset.univ.filter (· ≠ (0 : Fin (n + 1))),
      ∑ j : Fin d, (∏ t : Fin (n + 1), w t (x t)) * (p j (x i) * G i j ((fun m => (x m : U)) ∘ i.succAbove)) := by
    ext x
    rw [hdecomp (fun m => (x m : U))]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
  rw [hrew]
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro i hi
  rw [Finset.mem_filter] at hi
  rw [Finset.sum_comm]
  apply Finset.sum_eq_zero
  intro j _
  exact common_space_diagonal_tensor_rank_bound_term_sum_zero n d a h p h_ortho G i hi.2 j

open Classical in
theorem common_space_diagonal_tensor_rank_bound_single_term_nonzero {U : Type*} (n : ℕ) (_hn : 1 ≤ n) {V : Finset U} (a : V) (h : V → ℚ)
    (ha : h a ≠ 0) (f : (Fin (n + 1) → U) → ℚ)
    (hdiag : is_k_diagonal_on V f) :
    let w : Fin (n + 1) → V → ℚ := Fin.cons (fun u => if u = a then (1:ℚ) else 0) (fun _ => h)
    ∑ x : Fin (n + 1) → V, (∏ t : Fin (n + 1), w t (x t)) * f (fun m => (x m : U)) ≠ 0 := by
  intro w
  let x_diag : Fin (n + 1) → V := fun _ => a
  have h_term_zero : ∀ x : Fin (n + 1) → V, x ≠ x_diag →
      (∏ t : Fin (n + 1), w t (x t)) * f (fun m => (x m : U)) = 0 := by
    intro x hx
    by_cases h0 : x 0 = a
    · have h_not_all : ¬ (∀ i j : Fin (n + 1), (x i : U) = (x j : U)) := by
        intro hall
        apply hx
        ext i
        have hi0 := hall i 0
        have h0' : (x 0 : U) = (a : U) := congr_arg Subtype.val h0
        exact hi0.trans h0'
      have hf : f (fun m => (x m : U)) = 0 := by
        by_contra hfne
        have h_all_eq := (hdiag (fun m => (x m : U)) (fun m => (x m).2)).mp hfne
        exact h_not_all h_all_eq
      rw [hf, mul_zero]
    · have hw0 : w 0 (x 0) = 0 := by
        have : w 0 = fun u => if u = a then (1:ℚ) else 0 := Fin.cons_zero (α := fun _ => V → ℚ) _ _
        rw [this]
        dsimp
        exact if_neg h0
      have hprod : ∏ t : Fin (n + 1), w t (x t) = 0 := by
        rw [Fin.prod_univ_succ]
        rw [hw0, zero_mul]
      rw [hprod, zero_mul]
  have hsum_eq : ∑ x : Fin (n + 1) → V, (∏ t : Fin (n + 1), w t (x t)) * f (fun m => (x m : U)) =
      (∏ t : Fin (n + 1), w t (x_diag t)) * f (fun m => (x_diag m : U)) := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ x_diag)]
    have herase : ∑ x ∈ (Finset.univ.erase x_diag), (∏ t : Fin (n + 1), w t (x t)) * f (fun m => (x m : U)) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      rw [Finset.mem_erase] at hx
      exact h_term_zero x hx.1
    rw [herase, add_zero]
  rw [hsum_eq]
  have hf_diag : f (fun m => (x_diag m : U)) ≠ 0 := by
    have h_all : ∀ i j : Fin (n + 1), ((x_diag i : U) = (x_diag j : U)) := fun _ _ => rfl
    exact (hdiag (fun m => (x_diag m : U)) (fun m => (x_diag m).2)).mpr h_all
  have hprod_diag : ∏ t : Fin (n + 1), w t (x_diag t) ≠ 0 := by
    rw [Fin.prod_univ_succ]
    have hw0 : w 0 (x_diag 0) = 1 := by
      have : w 0 = fun u => if u = a then (1:ℚ) else 0 := Fin.cons_zero (α := fun _ => V → ℚ) _ _
      rw [this]
      dsimp [x_diag]
      rw [if_pos rfl]
    rw [hw0, one_mul]
    have hw_succ : ∀ i : Fin n, w i.succ (x_diag i.succ) = h a := by
      intro i
      have : w i.succ = h := Fin.cons_succ (α := fun _ => V → ℚ) _ _ i
      rw [this]
    have hprod_succ : ∏ i : Fin n, w i.succ (x_diag i.succ) = (h a) ^ n := by
      have : (fun i : Fin n => w i.succ (x_diag i.succ)) = fun _ => h a := by
        ext i; exact hw_succ i
      rw [this, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    rw [hprod_succ]
    exact pow_ne_zero n ha
  exact mul_ne_zero hprod_diag hf_diag

/-- Common-space diagonal tensor rank bound: a k-diagonal tensor on V decomposed via d functions in one variable has |V| ≤ d. -/
theorem common_space_diagonal_tensor_rank_bound
    {U : Type*} (n d : ℕ) (hn : 1 ≤ n) (V : Finset U)
    (f : (Fin (n + 1) → U) → ℚ)
    (hdiag : is_k_diagonal_on V f)
    (p : Fin d → (U → ℚ))
    (G : Fin (n + 1) → Fin d → (Fin n → U) → ℚ)
    (hdecomp : ∀ x : Fin (n + 1) → U,
      f x = ∑ i ∈ Finset.univ.filter (· ≠ (0 : Fin (n + 1))),
        ∑ j : Fin d, p j (x i) * G i j (x ∘ i.succAbove)) :
    V.card ≤ d := by
  classical
  by_contra! hcard
  rcases exists_nontrivial_solution_of_card_gt V d p hcard with ⟨h, hne, h_ortho⟩
  have hex : ∃ a : V, h a ≠ 0 := by
    by_contra! hall
    apply hne
    ext a
    exact hall a
  rcases hex with ⟨a, ha⟩
  have hzero := common_space_diagonal_tensor_rank_bound_total_sum_zero n d a h f p h_ortho G hdecomp
  have hnonzero := common_space_diagonal_tensor_rank_bound_single_term_nonzero n hn a h ha f hdiag
  exact hnonzero hzero
