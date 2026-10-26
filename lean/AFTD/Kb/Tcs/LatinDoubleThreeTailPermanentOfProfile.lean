import AFTD.Prelude
import AFTD.Kb.Tcs.LatinDoubleThreeTailShape
import AFTD.Kb.Tcs.LatinDoubleThreeTailProfile
import AFTD.Kb.Tcs.LatinTopRowAvailability
import AFTD.Kb.Tcs.LatinTopRowAvailabilityEqOneIff
import AFTD.Kb.Tcs.MatrixPermanentFromBlocksZeroOneTwo
import AFTD.Kb.Tcs.MemLatinColumnSymbols
import AFTD.Kb.Tcs.LatinColumnSymbols

/-!
# latin_double_three_tail_permanent_of_profile

Topic: combinatorics   Node: af4035bf5e52

Provenance: helper lemma. Helper for the open enumeration problem in https://arxiv.org/html/2610.29291v1, Conjecture 6.3, using the availability-permanent identity of Lemma 5.4. Exact computational route: experiments 4100, 4103 and 4106.

A filling with the canonical column profile has exactly four legal permutations for a new top row of length k+1.
-/

open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
namespace LatinTailProfilePermanent
private lemma permanent_equiv {α β : Type} [Fintype α] [DecidableEq α]
    [Fintype β] [DecidableEq β] (A : Matrix β β ℕ) (r c : α ≃ β) :
    (A.submatrix r c).permanent = A.permanent := by
  unfold Matrix.permanent
  refine Fintype.sum_equiv (Equiv.equivCongr c r) _ _ ?_
  intro σ
  refine Fintype.prod_equiv c _ _ ?_
  intro i
  simp only [Matrix.submatrix_apply,Equiv.equivCongr_apply_apply,Equiv.symm_apply_apply]

private lemma perm_has_rise {n : ℕ} (σ : Equiv.Perm (Fin n)) (hne : σ ≠ 1) :
    ∃ i, i.val < (σ i).val := by
  by_contra h
  push Not at h
  have hex : ∃ i, σ i ≠ i := by
    by_contra hh
    push Not at hh
    exact hne (by apply Equiv.ext; intro i; exact hh i)
  obtain ⟨i,hi⟩ := hex
  have hi' : (σ i).val ≠ i.val := fun he => hi (Fin.ext he)
  have hi_le := h i
  have hi_lt : (σ i).val < i.val := by omega
  have hsum := Finset.sum_lt_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin n))) => h j)
    ⟨i,Finset.mem_univ _,hi_lt⟩
  have heq := Equiv.sum_comp σ (fun j : Fin n => j.val)
  omega

private def stair (n : ℕ) : Matrix (Fin n) (Fin n) ℕ := fun i j => if i.val ≤ j.val then 1 else 0
private lemma permanent_stair (n : ℕ) : (stair n).permanent = 1 := by
  classical
  unfold Matrix.permanent
  have heq : (∑ σ : Equiv.Perm (Fin n), ∏ i : Fin n, stair n (σ i) i) =
      ∏ i : Fin n, stair n ((1 : Equiv.Perm (Fin n)) i) i := by
    apply Finset.sum_eq_single
    · intro σ _ hσ
      obtain ⟨i,hi⟩ := perm_has_rise σ hσ
      apply Finset.prod_eq_zero (Finset.mem_univ i)
      simp only [stair,show ¬ (σ i).val ≤ i.val by omega,ite_false]
    · simp
  simpa [stair] using heq

private def head (c : Fin 3) : Matrix (Fin 3) (Fin 3) ℕ := fun i j =>
  if i.val = 0 then 1 else if i.val = 1 then (if j ≠ c then 1 else 0)
    else if j = c then 1 else 0

private def tail (s : ℕ) : Matrix (Fin 3) (Fin 3) ℕ := fun i j =>
  if j.val = 0 then (if 3 - i.val = s then 1 else 0)
  else if j.val = 1 then (if 3 - i.val ≠ s then 1 else 0) else 1
private lemma head_perm : ∀ c : Fin 3, (head c).permanent = 2 := by decide
private lemma tail_perm : ∀ s : Fin 3, (tail (s.val+1)).permanent = 2 := by decide
private abbrev I (m : ℕ) := Fin 3 ⊕ (Fin m ⊕ Fin 3)
private def canonical (m : ℕ) (c : Fin 3) (s : ℕ) : Matrix (I m) (I m) ℕ :=
  Matrix.fromBlocks (head c) (Matrix.of fun _ _ => 1) 0
    (Matrix.fromBlocks (stair m) (Matrix.of fun _ _ => 1) 0 (tail s))
private lemma canonical_perm (m : ℕ) (c s : Fin 3) : (canonical m c (s.val+1)).permanent = 4 := by
  have hinner : (Matrix.fromBlocks (stair m) (Matrix.of fun _ _ => 1) 0 (tail (s.val+1))).permanent =
      (stair m).permanent * (tail (s.val+1)).permanent :=
    matrix_permanent_from_blocks_zero_one_two_zero_two_one _ _ _
  calc
    (canonical m c (s.val+1)).permanent = (head c).permanent *
        (Matrix.fromBlocks (stair m) (Matrix.of fun _ _ => 1) 0 (tail (s.val+1))).permanent :=
      matrix_permanent_from_blocks_zero_one_two_zero_two_one _ _ _
    _ = 4 := by rw [hinner,head_perm,tail_perm,permanent_stair]

private def cols (m : ℕ) : I m ≃ Fin (m+6) :=
  ((Equiv.sumCongr (Equiv.refl (Fin 3)) (finSumFinEquiv : Fin m ⊕ Fin 3 ≃ Fin (m+3))).trans
    (finSumFinEquiv : Fin 3 ⊕ Fin (m+3) ≃ Fin (3+(m+3)))).trans
    (finCongr (by omega))
private def rows (m : ℕ) : I m ≃ Fin (m+6) := (cols m).trans Fin.revPerm
private lemma cols_left (m : ℕ) (i : Fin 3) : (cols m (.inl i)).val = i.val := by rfl
private lemma cols_mid (m : ℕ) (i : Fin m) : (cols m (.inr (.inl i))).val = 3+i.val := by rfl
private lemma cols_tail (m : ℕ) (i : Fin 3) : (cols m (.inr (.inr i))).val = 3+(m+i.val) := by rfl
private lemma rows_val (m : ℕ) (x : I m) : (rows m x).val = m+6-((cols m x).val+1) := by rfl
end LatinTailProfilePermanent

open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
namespace LatinTailProfilePermanent

private def profile_sets (m : ℕ) (c : Fin 3) (s : ℕ) (j : Fin (m+6)) : Finset ℕ :=
  if j.val < 3 then
    (if j.val = c.val then Finset.Icc 1 (m+3) ∪ {m+5} else Finset.Icc 1 (m+4))
  else if j.val < m+3 then Finset.Icc 1 (m+5-j.val)
  else if j.val = m+3 then Finset.Icc 1 3 \ {s}
  else if j.val = m+4 then {s} else ∅

private def profile_matrix (m : ℕ) (c : Fin 3) (s : ℕ) : Matrix (Fin (m+6)) (Fin (m+6)) ℕ :=
  fun i j => if i.val+1 ∈ profile_sets m c s j then 0 else 1

private lemma rows_left_symbol (m : ℕ) (i : Fin 3) :
    (rows m (.inl i)).val+1 = m+6-i.val := by
  rw [rows_val,cols_left]
  omega
private lemma rows_mid_symbol (m : ℕ) (i : Fin m) :
    (rows m (.inr (.inl i))).val+1 = m+3-i.val := by
  rw [rows_val,cols_mid]
  omega
private lemma rows_tail_symbol (m : ℕ) (i : Fin 3) :
    (rows m (.inr (.inr i))).val+1 = 3-i.val := by
  rw [rows_val,cols_tail]
  omega

private lemma sets_left (m : ℕ) (c : Fin 3) (s : ℕ) (j : Fin 3) :
    profile_sets m c s (cols m (.inl j)) =
      if j = c then Finset.Icc 1 (m+3) ∪ {m+5} else Finset.Icc 1 (m+4) := by
  simp only [profile_sets,cols_left,j.isLt,ite_true,Fin.ext_iff]

private lemma sets_mid (m : ℕ) (c : Fin 3) (s : ℕ) (j : Fin m) :
    profile_sets m c s (cols m (.inr (.inl j))) = Finset.Icc 1 (m+2-j.val) := by
  have h0 : ¬ 3+j.val < 3 := by omega
  have h1 : 3+j.val < m+3 := by omega
  simp only [profile_sets,cols_mid,h0,h1,ite_false,ite_true]
  congr 1
  omega

private lemma sets_tail (m : ℕ) (c : Fin 3) (s : ℕ) (j : Fin 3) :
    profile_sets m c s (cols m (.inr (.inr j))) =
      if j.val = 0 then Finset.Icc 1 3 \ {s} else if j.val = 1 then {s} else ∅ := by
  have h0 : ¬ 3+(m+j.val) < 3 := by omega
  have h1 : ¬ 3+(m+j.val) < m+3 := by omega
  have h2 : (3+(m+j.val) = m+3) ↔ j.val = 0 := by omega
  have h3 : (3+(m+j.val) = m+4) ↔ j.val = 1 := by omega
  simp only [profile_sets,cols_tail,h0,h1,h2,h3,ite_false]

private lemma low_pair_mem (i s : Fin 3) :
    3-i.val ∈ (Finset.Icc 1 3 \ {s.val+1}) ↔ 3-i.val ≠ s.val+1 := by
  rw [Finset.mem_sdiff,Finset.mem_Icc,Finset.mem_singleton]
  constructor
  · exact fun h => h.2
  · intro h
    exact ⟨⟨by omega,by omega⟩,h⟩

private lemma profile_reindex (m : ℕ) (c s : Fin 3) :
    (profile_matrix m c (s.val+1)).submatrix (rows m) (cols m) = canonical m c (s.val+1) := by
  ext x y
  rcases x with i | (i | i) <;> rcases y with j | (j | j)
  all_goals simp only [Matrix.submatrix_apply,profile_matrix,
    rows_left_symbol,rows_mid_symbol,rows_tail_symbol,
    sets_left,sets_mid,sets_tail,canonical,
    Matrix.fromBlocks_apply₁₁,Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁,Matrix.fromBlocks_apply₂₂,Matrix.of_apply,Matrix.zero_apply,
    head,tail,stair]
  all_goals split_ifs at *
  all_goals (try simp_rw [low_pair_mem] at *)
  all_goals (try simp_all only [Finset.mem_Icc,Finset.mem_union,
    Finset.mem_singleton,Finset.mem_sdiff,Finset.notMem_empty,Fin.ext_iff])
  all_goals try omega

private lemma profile_permanent (m : ℕ) (c s : Fin 3) :
    (profile_matrix m c (s.val+1)).permanent = 4 := by
  rw [← permanent_equiv _ (rows m) (cols m),profile_reindex]
  exact canonical_perm m c s

end LatinTailProfilePermanent

open scoped BigOperators
set_option maxHeartbeats 1000000
set_option maxRecDepth 4000
namespace LatinTailProfilePermanent
private abbrev D (m : ℕ) := latin_double_three_tail_shape (m+5)

private lemma availability_entry (d : YoungDiagram) (T : d.cells → ℕ) (w : ℕ) (i j : Fin w) :
    latin_top_row_availability d T w i j =
      if i.val+1 ∈ latin_column_symbols d T j.val then 0 else 1 := by
  have h : (∀ a : d.cells, a.val.2 = j.val → T a ≠ i.val+1) ↔
      i.val+1 ∉ latin_column_symbols d T j.val := by
    constructor
    · intro hP hmem
      obtain ⟨a,ha,hval⟩ := (mem_latin_column_symbols d T j.val (i.val+1)).mp hmem
      exact hP a ha hval
    · intro hP a ha hval
      exact hP ((mem_latin_column_symbols d T j.val (i.val+1)).mpr ⟨a,ha,hval⟩)
  simp only [latin_top_row_availability,h,ite_not]

private lemma empty_column (m : ℕ) (T : (D m).cells → ℕ) :
    latin_column_symbols (D m) T (m+5) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  obtain ⟨a,ha,_⟩ := (mem_latin_column_symbols _ _ _ _).mp hx
  have hm := a.property
  simp only [D,latin_double_three_tail_shape,Finset.mem_filter,Finset.mem_product,Finset.mem_range] at hm
  have hb := hm.1.2
  have hb' : a.val.2 < m+5 := lt_of_lt_of_le hb (max_le le_rfl (by omega))
  omega

private lemma availability_of_profile (m : ℕ) (T : (D m).cells → ℕ)
    (hp : latin_double_three_tail_profile (m+5) T) :
    ∃ c s : Fin 3, latin_top_row_availability (D m) T (m+6) = profile_matrix m c (s.val+1) := by
  obtain ⟨snat,hs,cnat,hc,hfirst,hmid,hpair,hlast⟩ := hp
  have hs' := Finset.mem_Icc.mp hs
  let c : Fin 3 := ⟨cnat,hc⟩
  let s : Fin 3 := ⟨snat-1,by omega⟩
  have hsnat : s.val+1 = snat := by dsimp [s]; omega
  have hk2 : m+5-2 = m+3 := by omega
  have hk1 : m+5-1 = m+4 := by omega
  simp only [hk2,hk1] at hfirst hmid hpair hlast
  rw [← hsnat] at hpair hlast
  refine ⟨c,s,?_⟩
  have hsets (j : Fin (m+6)) :
      latin_column_symbols (D m) T j.val = profile_sets m c (s.val+1) j := by
    by_cases h0 : j.val < 3
    · rw [profile_sets,if_pos h0]
      exact hfirst j.val h0
    · by_cases h1 : j.val < m+3
      · rw [profile_sets,if_neg h0,if_pos h1]
        exact hmid j.val (by omega) h1
      · by_cases h2 : j.val = m+3
        · rw [profile_sets,if_neg h0,if_neg h1,if_pos h2,h2]
          exact hpair
        · by_cases h3 : j.val = m+4
          · rw [profile_sets,if_neg h0,if_neg h1,if_neg h2,if_pos h3,h3]
            exact hlast
          · have hj : j.val = m+5 := by omega
            rw [profile_sets,if_neg h0,if_neg h1,if_neg h2,if_neg h3]
            rw [hj,empty_column]
  ext i j
  rw [availability_entry,hsets]
  rfl

private lemma target (k : ℕ) (hk : 5 ≤ k) (T : (latin_double_three_tail_shape k).cells → ℕ)
    (hp : latin_double_three_tail_profile k T) :
    Matrix.permanent (latin_top_row_availability (latin_double_three_tail_shape k) T (k+1)) = 4 := by
  obtain ⟨m,rfl⟩ : ∃ m, k = m+5 := ⟨k-5,by omega⟩
  obtain ⟨c,s,heq⟩ := availability_of_profile m T hp
  change (latin_top_row_availability (D m) T (m+6)).permanent = 4
  rw [heq]
  exact profile_permanent m c s
end LatinTailProfilePermanent

theorem latin_double_three_tail_permanent_of_profile (k : ℕ) (hk : 5 ≤ k) (T : (latin_double_three_tail_shape k).cells → ℕ) (hp : latin_double_three_tail_profile k T) : Matrix.permanent (latin_top_row_availability (latin_double_three_tail_shape k) T (k+1)) = 4 := by
  exact LatinTailProfilePermanent.target k hk T hp
