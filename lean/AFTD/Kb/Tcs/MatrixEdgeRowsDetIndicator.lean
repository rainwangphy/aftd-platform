import AFTD.Prelude

/-!
# matrix_edge_rows_det_indicator

Topic: graphs   Node: 78a631a71bcb

Provenance: helper lemma. step towards tournament_arborescence_hadamard_bound

Let g be a self-map of Fin n with g r = r and with no fixed point other than r. Let C be the matrix indexed by the vertices ≠ r whose (i,j) entry is [i = j] - [g i = j]. Then det C equals 1 if iterating g n times from every vertex lands in r, and 0 otherwise.
-/

open Finset Matrix Fintype Function

def matrix_edge_rows_det_indicator_rank {n : ℕ} (g : Fin n → Fin n) (r : Fin n) (v : Fin n) : ℕ :=
  ∑ k ∈ range (n + 1), if g^[k] v = r then 1 else 0

lemma matrix_edge_rows_det_indicator_rank_apply_succ {n : ℕ} (g : Fin n → Fin n) (r : Fin n)
    (hr : g r = r) (hn : ∀ v, g^[n] v = r) (v : Fin n) (hv : v ≠ r) :
    matrix_edge_rows_det_indicator_rank g r (g v) = matrix_edge_rows_det_indicator_rank g r v + 1 := by
  have h1 : matrix_edge_rows_det_indicator_rank g r (g v) =
      (∑ x ∈ range n, if g^[x] (g v) = r then 1 else 0) +
        if g^[n] (g v) = r then 1 else 0 := by
    exact sum_range_succ (fun k => if g^[k] (g v) = r then 1 else 0) n
  have h2 : matrix_edge_rows_det_indicator_rank g r v =
      (∑ x ∈ range n, if g^[x + 1] v = r then 1 else 0) +
        if g^[0] v = r then 1 else 0 := by
    exact sum_range_succ' (fun k => if g^[k] v = r then 1 else 0) n
  have h0 : (if g^[0] v = r then 1 else 0) = 0 := if_neg hv
  have hn1 : (if g^[n] (g v) = r then 1 else 0) = 1 := by
    have : g^[n] (g v) = r := by
      rw [← Function.iterate_succ_apply, Function.iterate_succ_apply', hn v, hr]
    simp [this]
  have hmid : ∑ x ∈ range n, (if g^[x] (g v) = r then 1 else 0) =
      ∑ x ∈ range n, (if g^[x + 1] v = r then 1 else 0) := by
    refine sum_congr rfl fun x _ => ?_
    rw [← Function.iterate_succ_apply g x v]
  rw [h1, h2, h0, hn1, hmid, add_zero]

lemma matrix_edge_rows_det_indicator_sum_subtype_ite_eq {n : ℕ} (r : Fin n) (x : Fin n) (hx : x ≠ r)
    (f : {i : Fin n // i ≠ r} → ℝ) :
    ∑ i : {i : Fin n // i ≠ r}, (if i.1 = x then (1 : ℝ) else 0) * f i = f ⟨x, hx⟩ := by
  have : ∑ i : {i : Fin n // i ≠ r}, (if i.1 = x then (1 : ℝ) else 0) * f i =
      ∑ i : {i : Fin n // i ≠ r}, (if i = ⟨x, hx⟩ then (1 : ℝ) else 0) * f i := by
    refine sum_congr rfl fun ⟨i, hi⟩ _ => ?_
    by_cases h : i = x
    · have h_eq : (⟨i, hi⟩ : {i : Fin n // i ≠ r}) = ⟨x, hx⟩ := Subtype.ext h
      simp [h]
    · have h_ne : (⟨i, hi⟩ : {i : Fin n // i ≠ r}) ≠ ⟨x, hx⟩ := by
        intro h_eq
        exact h (congr_arg Subtype.val h_eq)
      simp [h, h_ne]
  rw [this]
  simp

lemma matrix_edge_rows_det_indicator_telescoping {n : ℕ} (g : Fin n → Fin n) (a : Fin n) (p : ℕ)
    (hcyc : g^[p] a = a) (k : Fin n) :
    ∑ t ∈ range p, (((if g^[t] a = k then (1 : ℝ) else 0)) - (if g^[t + 1] a = k then (1 : ℝ) else 0)) = 0 := by
  have := sum_range_sub' (fun t => if g^[t] a = k then (1 : ℝ) else 0) p
  rw [this]
  have h0 : g^[0] a = a := rfl
  rw [h0, hcyc, sub_self]

lemma matrix_edge_rows_det_indicator_case_b {n : ℕ} (g : Fin n → Fin n) (r : Fin n)
    (a : Fin n) (p : ℕ) (hp : 0 < p) (hcyc : g^[p] a = a) (htr : ∀ t < p, g^[t] a ≠ r) :
    (Matrix.of (fun (i : {i : Fin n // i ≠ r}) (j : {j : Fin n // j ≠ r}) =>
      (if (i : Fin n) = j.1 then (1 : ℝ) else 0) - (if g (i : Fin n) = (j : Fin n) then (1 : ℝ) else 0))).det = 0 := by
  let I := {i : Fin n // i ≠ r}
  let C : Matrix I I ℝ := Matrix.of (fun i j =>
    (if (i : Fin n) = j.1 then (1 : ℝ) else 0) - (if g (i : Fin n) = (j : Fin n) then (1 : ℝ) else 0))
  let w : I → ℝ := fun j => ∑ t ∈ range p, if j.1 = g^[t] a then (1 : ℝ) else 0
  have h_mul : w ᵥ* C = 0 := by
    ext k
    simp only [vecMul, dotProduct, Pi.zero_apply]
    have : ∑ i : I, w i * C i k =
        ∑ t ∈ range p, (((if g^[t] a = k.1 then (1 : ℝ) else 0)) - (if g^[t + 1] a = k.1 then (1 : ℝ) else 0)) := by
      dsimp [w]
      simp_rw [sum_mul]
      rw [sum_comm]
      refine sum_congr rfl fun t ht => ?_
      have ht_ne : g^[t] a ≠ r := htr t (mem_range.mp ht)
      have := matrix_edge_rows_det_indicator_sum_subtype_ite_eq r (g^[t] a) ht_ne (fun i => C i k)
      rw [this]
      dsimp [C]
      have hstep : g (g^[t] a) = g^[t + 1] a := (Function.iterate_succ_apply' g t a).symm
      rw [hstep]
      rfl
    rw [this, matrix_edge_rows_det_indicator_telescoping g a p hcyc k.1]
  have a_ne_r : a ≠ r := by
    have := htr 0 hp
    rwa [Function.iterate_zero_apply] at this
  let a_I : I := ⟨a, a_ne_r⟩
  have hw_a : w a_I ≠ 0 := by
    dsimp [w]
    rw [← sum_erase_add _ _ (mem_range.mpr hp)]
    have : (if a_I.1 = g^[0] a then (1 : ℝ) else 0) = 1 := by
      simp [a_I]
    rw [this]
    have : 0 ≤ ∑ x ∈ (range p).erase 0, if a_I.1 = g^[x] a then (1 : ℝ) else 0 := by
      refine sum_nonneg fun x _ => ?_
      split_ifs <;> norm_num
    linarith
  rw [← det_transpose]
  have h1 : Cᵀ *ᵥ w = 0 := by
    rw [← vecMul_transpose]
    exact h_mul
  have hi' : w a_I ∈ nonZeroDivisors ℝ := mem_nonZeroDivisors_of_ne_zero hw_a
  exact det_eq_zero_of_mulVec_eq_zero_of_mem_nonZeroDivisors h1 hi'

lemma matrix_edge_rows_det_indicator_exists_cycle {n : ℕ} (g : Fin n → Fin n) (r : Fin n)
    (hr : g r = r) (v : Fin n) (hvn : g^[n] v ≠ r) :
    ∃ (a : Fin n) (p : ℕ), 0 < p ∧ g^[p] a = a ∧ ∀ t < p, g^[t] a ≠ r := by
  let f : Fin (n + 1) → Fin n := fun k => g^[k.1] v
  have h_card : card (Fin n) < card (Fin (n + 1)) := by simp
  have h_not_inj : ¬ Injective f := not_injective_of_card_lt f h_card
  rw [not_injective_iff] at h_not_inj
  obtain ⟨x, y, hxy_eq, hxy_ne⟩ := h_not_inj
  obtain ⟨k, l, hkl, hle, h_eq⟩ : ∃ k l : ℕ, k < l ∧ l ≤ n ∧ g^[k] v = g^[l] v := by
    rcases lt_or_gt_of_ne hxy_ne with hlt | hgt
    · exact ⟨x.1, y.1, hlt, Nat.le_of_lt_succ y.2, hxy_eq⟩
    · exact ⟨y.1, x.1, hgt, Nat.le_of_lt_succ x.2, hxy_eq.symm⟩
  refine ⟨g^[k] v, l - k, Nat.sub_pos_of_lt hkl, ?_, ?_⟩
  · have : l - k + k = l := Nat.sub_add_cancel (Nat.le_of_lt hkl)
    have h_split : g^[l - k] (g^[k] v) = g^[l - k + k] v := by
      rw [← Function.iterate_add_apply]
    rw [h_split, this, h_eq]
  · intro t ht h_r
    have h_iter : g^[n] v = r := by
      have ht_le : t + k ≤ n := by omega
      have h1 : g^[t + k] v = r := by
        rw [Function.iterate_add_apply]
        exact h_r
      have h2 : g^[n - (t + k)] (g^[t + k] v) = g^[n - (t + k)] r := by rw [h1]
      have h3 : g^[n - (t + k)] r = r := by
        induction (n - (t + k)) with
        | zero => rfl
        | succ m ih => rw [Function.iterate_succ_apply', ih, hr]
      have h4 : g^[n - (t + k)] (g^[t + k] v) = g^[n] v := by
        rw [← Function.iterate_add_apply, Nat.sub_add_cancel ht_le]
      rw [h4, h3] at h2
      exact h2
    exact hvn h_iter

/-- The `0`/`1` determinant lemma behind the directed matrix-tree theorem: rows `e_i - e_{g i}` on the vertices other than the root give determinant one exactly for spanning in-arborescences towards the root. -/
theorem matrix_edge_rows_det_indicator {n : ℕ} (g : Fin n → Fin n) (r : Fin n) (hr : g r = r) (hne : ∀ v, v ≠ r → g v ≠ v) : (Matrix.of (fun (i : {i : Fin n // i ≠ r}) (j : {j : Fin n // j ≠ r}) => (if (i : Fin n) = j.1 then (1 : ℝ) else 0) - (if g (i : Fin n) = (j : Fin n) then (1 : ℝ) else 0))).det = if (∀ v : Fin n, g^[n] v = r) then (1 : ℝ) else 0 := by
  by_cases hn : ∀ v : Fin n, g^[n] v = r
  · rw [if_pos hn]
    let I := {i : Fin n // i ≠ r}
    let f : I → Lex (ℕ × ℕ) := fun i => toLex (matrix_edge_rows_det_indicator_rank g r i.1, (i.1 : ℕ))
    have hf_inj : Function.Injective f := by
      intro i j hij
      have hpair := congr_arg ofLex hij
      have h2 := congr_arg Prod.snd hpair
      exact Subtype.ext (Fin.ext h2)
    let instLO : LinearOrder I := LinearOrder.lift' f hf_inj
    let C : Matrix I I ℝ := Matrix.of (fun i j =>
      (if (i : Fin n) = j.1 then (1 : ℝ) else 0) - (if g (i : Fin n) = (j : Fin n) then (1 : ℝ) else 0))
    have h_tri : @Matrix.IsUpperTriangular I ℝ _ instLO.toLT C := by
      intro i j (hjlt : f j < f i)
      dsimp [C]
      have hij_ne : (i : Fin n) ≠ j.1 := by
        intro h
        have hij : i = j := Subtype.ext h
        subst hij
        exact lt_irrefl (f i) hjlt
      have hg_ne : g (i : Fin n) ≠ (j : Fin n) := by
        intro hg
        have h_rank : matrix_edge_rows_det_indicator_rank g r (g i.1) = matrix_edge_rows_det_indicator_rank g r i.1 + 1 :=
          matrix_edge_rows_det_indicator_rank_apply_succ g r hr hn i.1 i.2
        have hj_rank : matrix_edge_rows_det_indicator_rank g r j.1 = matrix_edge_rows_det_indicator_rank g r i.1 + 1 := by rw [← hg, h_rank]
        have hf_lt : f i < f j := by
          dsimp [f]
          apply Prod.Lex.left
          rw [hj_rank]
          exact Nat.lt_succ_self (matrix_edge_rows_det_indicator_rank g r (i : Fin n))
        exact lt_asymm hjlt hf_lt
      have h1 : (if (i : Fin n) = j.1 then (1 : ℝ) else 0) = 0 := if_neg hij_ne
      have h2 : (if g (i : Fin n) = (j : Fin n) then (1 : ℝ) else 0) = 0 := if_neg hg_ne
      rw [h1, h2, sub_zero]
    rw [@Matrix.det_of_isUpperTriangular I ℝ C _ _ _ instLO h_tri]
    have hdiag : ∀ i : I, C i i = 1 := by
      intro i
      dsimp [C]
      have : g (i : Fin n) ≠ (i : Fin n) := hne i.1 i.2
      simp [this]
    simp [hdiag]
  · rw [if_neg hn]
    have hn' : ∃ v, g^[n] v ≠ r := by
      contrapose! hn
      exact hn
    obtain ⟨v, hv⟩ := hn'
    obtain ⟨a, p, hp, hcyc, htr⟩ := matrix_edge_rows_det_indicator_exists_cycle g r hr v hv
    exact matrix_edge_rows_det_indicator_case_b g r a p hp hcyc htr
