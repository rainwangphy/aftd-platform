import AFTD.Prelude
import AFTD.Kb.Tcs.MagicSquareWinningOp
import AFTD.Kb.Tcs.MagicSquareWinningOpDetRow0
import AFTD.Kb.Tcs.IsPovm
import AFTD.Kb.Tcs.MagicSquareEvenDiffCardTwo

/-!
# magic_square_winning_op_sub_det_row0_le

Topic: quantum   Node: 375981fb515f

Provenance: formalization of a published result. Source: arXiv:2610.12001, page 20, equation (24)

For any valid measurement effects A for Alice and B for Bob in the magic square game (where each A x is a POVM with support on even strings and each B j is a POVM with support on odd strings) and any even sign string k : Fin 3 → Bool (with parity check xor (xor (k 0) (k 1)) (k 2) = false), the difference between the bipartite winning operator magic_square_winning_op A B and the deterministic row-0 operator magic_square_winning_op_det_row0 A B k is bounded above in the Loewner order by (2 / 9 : ℂ) • (((1 : Matrix (Fin dA) (Fin dA) ℂ) - A 0 k) ⊗ₖ (1 : Matrix (Fin dB) (Fin dB) ℂ)).
-/

open scoped ComplexOrder MatrixOrder Kronecker

private lemma msd_kronecker_sub {l m n p : Type}
    (X Y : Matrix l m ℂ) (Z : Matrix n p ℂ) :
    (X - Y) ⊗ₖ Z = X ⊗ₖ Z - Y ⊗ₖ Z := by
  have h : (X - Y) ⊗ₖ Z + Y ⊗ₖ Z = X ⊗ₖ Z := by
    rw [← Matrix.add_kronecker, sub_add_cancel]
  exact eq_sub_of_add_eq h

private lemma msd_finset_sum_kronecker {ι l m n p : Type}
    (s : Finset ι) (X : ι → Matrix l m ℂ) (Z : Matrix n p ℂ) :
    (∑ i ∈ s, X i) ⊗ₖ Z = ∑ i ∈ s, X i ⊗ₖ Z := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Matrix.add_kronecker, ih]

private lemma msd_finset_sum_kronecker_right {ι l m n p : Type}
    (s : Finset ι) (X : Matrix l m ℂ) (Z : ι → Matrix n p ℂ) :
    X ⊗ₖ (∑ i ∈ s, Z i) = ∑ i ∈ s, X ⊗ₖ Z i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, Matrix.kronecker_add, ih]

private lemma msd_psd_sum {ι : Type} [Fintype ι] {n : Type} (F : ι → Matrix n n ℂ)
    (h : ∀ i, (F i).PosSemidef) : (∑ i, F i).PosSemidef := by
  classical
  apply Finset.sum_induction F (fun M => M.PosSemidef)
    (fun a b ha hb => ha.add hb) Matrix.PosSemidef.zero
  intro i _
  exact h i

private lemma msd_sum_sub_sum {n : Type} {ι₁ ι₂ ι₃ : Type} [Fintype ι₁] [Fintype ι₂] [Fintype ι₃]
    (F G : ι₁ → ι₂ → ι₃ → Matrix n n ℂ) :
    (∑ i, ∑ j, ∑ l, F i j l) - (∑ i, ∑ j, ∑ l, G i j l) =
      ∑ i, ∑ j, ∑ l, (F i j l - G i j l) := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro i _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro j _
  rw [← Finset.sum_sub_distrib]

private lemma msd_coeff_nonneg (s k c : Fin 3 → Bool) (j : Fin 3) :
    (0:ℂ) ≤ ((if s j ≠ k j then (1:ℂ) else 0) -
      ((if s j = c 0 then (1:ℂ) else 0) - (if k j = c 0 then (1:ℂ) else 0))) := by
  by_cases h1 : s j = k j
  · rw [if_neg (fun h => h h1)]
    by_cases h2 : s j = c 0
    · have h3 : k j = c 0 := by rw [← h1]; exact h2
      rw [if_pos h2, if_pos h3]; norm_num
    · have h3 : ¬ (k j = c 0) := by rw [← h1]; exact h2
      rw [if_neg h2, if_neg h3]; norm_num
  · rw [if_pos h1]
    by_cases h2 : s j = c 0
    · have h3 : ¬ (k j = c 0) := fun h => h1 (by rw [h2, h])
      rw [if_pos h2, if_neg h3]; norm_num
    · rw [if_neg h2]
      by_cases h3 : k j = c 0
      · rw [if_pos h3]; norm_num
      · rw [if_neg h3]; norm_num

private lemma msd_coeff_psd {dA dB : ℕ}
    (A : Fin 3 → (Fin 3 → Bool) → Matrix (Fin dA) (Fin dA) ℂ)
    (B : Fin 3 → (Fin 3 → Bool) → Matrix (Fin dB) (Fin dB) ℂ)
    (k : Fin 3 → Bool)
    (hA_povm : ∀ x, is_povm dA (A x))
    (hB_povm : ∀ j, is_povm dB (B j)) :
    ((∑ j, ∑ s, ∑ c, (((if s j ≠ k j then (1:ℂ) else 0) -
        ((if s j = c 0 then (1:ℂ) else 0) - (if k j = c 0 then (1:ℂ) else 0))) • (A 0 s ⊗ₖ B j c)))).PosSemidef := by
  apply msd_psd_sum
  intro j
  apply msd_psd_sum
  intro s
  apply msd_psd_sum
  intro c
  exact Matrix.PosSemidef.smul (Matrix.PosSemidef.kronecker ((hA_povm 0).1 s) ((hB_povm j).1 c))
    (msd_coeff_nonneg s k c j)

private lemma msd_double {dA dB : ℕ}
    (P Q : (Fin 3 → Bool) → Matrix (Fin dA) (Fin dA) ℂ)
    (B : Fin 3 → (Fin 3 → Bool) → Matrix (Fin dB) (Fin dB) ℂ) (x : Fin 3) :
    (∑ j, ∑ s, ∑ c, (if s j = c x then (P s ⊗ₖ B j c) else 0))
    - (∑ j, ∑ s, ∑ c, (if s j = c x then (Q s ⊗ₖ B j c) else 0))
    = ∑ j, ∑ s, ∑ c, (if s j = c x then ((P s - Q s) ⊗ₖ B j c) else 0) := by
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro j _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro s _
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl; intro c _
  by_cases h : s j = c x
  · rw [if_pos h, if_pos h, if_pos h, ← msd_kronecker_sub]
  · rw [if_neg h, if_neg h, if_neg h, sub_self]

private lemma msd_W_sub_Wd_eq {dA dB : ℕ}
    (A : Fin 3 → (Fin 3 → Bool) → Matrix (Fin dA) (Fin dA) ℂ)
    (B : Fin 3 → (Fin 3 → Bool) → Matrix (Fin dB) (Fin dB) ℂ)
    (k : Fin 3 → Bool) :
    magic_square_winning_op A B - magic_square_winning_op_det_row0 A B k =
      (1/9 : ℂ) • ∑ j, ∑ s, ∑ c,
        (if s j = c 0 then ((A 0 s - (if s = k then (1:Matrix (Fin dA) (Fin dA) ℂ) else 0)) ⊗ₖ B j c) else 0) := by
  let A' : Fin 3 → (Fin 3 → Bool) → Matrix (Fin dA) (Fin dA) ℂ :=
    fun x s => if x = 0 then (if s = k then 1 else 0) else A x s
  have hdet : magic_square_winning_op_det_row0 A B k = magic_square_winning_op A' B := rfl
  rw [hdet]
  unfold magic_square_winning_op
  rw [← smul_sub]
  congr 1
  rw [← Finset.sum_sub_distrib]
  trans (∑ j, ∑ s, ∑ c,
        (if s j = c 0 then ((A 0 s - (if s = k then (1:Matrix (Fin dA) (Fin dA) ℂ) else 0)) ⊗ₖ B j c) else 0))
  · rw [Finset.sum_eq_single 0]
    · simp only [A']
      exact msd_double (fun s => A 0 s) (fun s => (if s = k then (1:Matrix (Fin dA) (Fin dA) ℂ) else 0)) B 0
    · intro b _ hb
      have hAb : ∀ s, A' b s = A b s := by intro s; simp [A', hb]
      have hEq : (∑ j, ∑ s, ∑ c, (if s j = c b then (A b s ⊗ₖ B j c) else 0))
               = (∑ j, ∑ s, ∑ c, (if s j = c b then (A' b s ⊗ₖ B j c) else 0)) := by
        apply Finset.sum_congr rfl; intro j _
        apply Finset.sum_congr rfl; intro s _
        apply Finset.sum_congr rfl; intro c _
        rw [hAb s]
      rw [hEq, sub_self]
    · intro h; exact absurd (Finset.mem_univ 0) h
  · rfl

private lemma msd_Xcollapse {dA dB : ℕ}
    (B : Fin 3 → (Fin 3 → Bool) → Matrix (Fin dB) (Fin dB) ℂ)
    (k : Fin 3 → Bool) (j : Fin 3) (c : Fin 3 → Bool) :
    (∑ s : Fin 3 → Bool, (if s j = c 0 then (((if s = k then (1:ℂ) else 0)) • ((1:Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ B j c)) else 0))
    = (if k j = c 0 then ((1:Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ B j c) else 0) := by
  rw [Finset.sum_eq_single k]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ k) h

private lemma msd_L1 {dA dB : ℕ}
    (A : Fin 3 → (Fin 3 → Bool) → Matrix (Fin dA) (Fin dA) ℂ)
    (B : Fin 3 → (Fin 3 → Bool) → Matrix (Fin dB) (Fin dB) ℂ)
    (k : Fin 3 → Bool) :
    (∑ j, ∑ s, ∑ c, (if s j = c 0 then ((A 0 s - (if s = k then (1:Matrix (Fin dA) (Fin dA) ℂ) else 0)) ⊗ₖ B j c) else 0))
    = (∑ j, ∑ s, ∑ c, (if s j = c 0 then (A 0 s ⊗ₖ B j c) else 0))
      - (∑ j, ∑ c, (if k j = c 0 then ((1:Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ B j c) else 0)) := by
  have hsplit : (∑ j, ∑ s, ∑ c, (if s j = c 0 then ((A 0 s - (if s = k then (1:Matrix (Fin dA) (Fin dA) ℂ) else 0)) ⊗ₖ B j c) else 0))
      = (∑ j, ∑ s, ∑ c, (if s j = c 0 then (A 0 s ⊗ₖ B j c) else 0))
        - (∑ j, ∑ s, ∑ c, (if s j = c 0 then (((if s = k then (1:ℂ) else 0)) • ((1:Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ B j c)) else 0)) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro j _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro s _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro c _
    by_cases h : s j = c 0
    · rw [if_pos h, if_pos h, if_pos h, msd_kronecker_sub]
      congr 1
      by_cases hs : s = k
      · simp [hs]
      · simp [hs]
    · simp [h]
  rw [hsplit, sub_right_inj]
  apply Finset.sum_congr rfl; intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro c _
  exact msd_Xcollapse B k j c

private lemma msd_ite_split2 {dA dB : ℕ}
    (A : Fin 3 → (Fin 3 → Bool) → Matrix (Fin dA) (Fin dA) ℂ)
    (B : Fin 3 → (Fin 3 → Bool) → Matrix (Fin dB) (Fin dB) ℂ)
    (k : Fin 3 → Bool) (j : Fin 3) (s c : Fin 3 → Bool) :
    (((if s j = c 0 then (1:ℂ) else 0) - (if k j = c 0 then (1:ℂ) else 0)) • (A 0 s ⊗ₖ B j c))
    = (if s j = c 0 then (A 0 s ⊗ₖ B j c) else 0) - ((if k j = c 0 then (1:ℂ) else 0) • (A 0 s ⊗ₖ B j c)) := by
  by_cases h1 : s j = c 0 <;> by_cases h2 : k j = c 0 <;> simp [h1, h2]

private lemma msd_W2inner {dA dB : ℕ}
    (A : Fin 3 → (Fin 3 → Bool) → Matrix (Fin dA) (Fin dA) ℂ)
    (B : Fin 3 → (Fin 3 → Bool) → Matrix (Fin dB) (Fin dB) ℂ)
    (k : Fin 3 → Bool) (hA0 : (∑ s, A 0 s) = 1) (j : Fin 3) (c : Fin 3 → Bool) :
    (∑ s, ((if k j = c 0 then (1:ℂ) else 0) • (A 0 s ⊗ₖ B j c)))
    = (if k j = c 0 then ((1:Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ B j c) else 0) := by
  rw [← Finset.smul_sum]
  rw [← msd_finset_sum_kronecker]
  rw [hA0]
  by_cases h : k j = c 0
  · simp [h]
  · simp [h]

private lemma msd_L2 {dA dB : ℕ}
    (A : Fin 3 → (Fin 3 → Bool) → Matrix (Fin dA) (Fin dA) ℂ)
    (B : Fin 3 → (Fin 3 → Bool) → Matrix (Fin dB) (Fin dB) ℂ)
    (k : Fin 3 → Bool)
    (hA_povm : ∀ x, is_povm dA (A x)) :
    (∑ j, ∑ s, ∑ c, (((if s j = c 0 then (1:ℂ) else 0) - (if k j = c 0 then (1:ℂ) else 0)) • (A 0 s ⊗ₖ B j c)))
    = (∑ j, ∑ s, ∑ c, (if s j = c 0 then (A 0 s ⊗ₖ B j c) else 0))
      - (∑ j, ∑ c, (if k j = c 0 then ((1:Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ B j c) else 0)) := by
  have hsplit : (∑ j, ∑ s, ∑ c, (((if s j = c 0 then (1:ℂ) else 0) - (if k j = c 0 then (1:ℂ) else 0)) • (A 0 s ⊗ₖ B j c)))
      = (∑ j, ∑ s, ∑ c, (if s j = c 0 then (A 0 s ⊗ₖ B j c) else 0))
        - (∑ j, ∑ s, ∑ c, ((if k j = c 0 then (1:ℂ) else 0) • (A 0 s ⊗ₖ B j c))) := by
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro j _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro s _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro c _
    exact msd_ite_split2 A B k j s c
  rw [hsplit, sub_right_inj]
  apply Finset.sum_congr rfl; intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl; intro c _
  exact msd_W2inner A B k (hA_povm 0).2 j c

private lemma msd_coeff_smul {dA : ℕ}
    (A : Fin 3 → (Fin 3 → Bool) → Matrix (Fin dA) (Fin dA) ℂ)
    (k : Fin 3 → Bool)
    (hA_even : ∀ x s, (s 0 ^^ s 1 ^^ s 2) = true → A x s = 0)
    (hk : (k 0 ^^ k 1 ^^ k 2) = false)
    (s : Fin 3 → Bool) :
    (∑ j : Fin 3, (if s j ≠ k j then (1:ℂ) else 0)) • (A 0 s)
    = (2:ℂ) • (if s = k then (0:Matrix (Fin dA) (Fin dA) ℂ) else A 0 s) := by
  by_cases hs : s = k
  · rw [hs]; simp
  · cases hbool : (s 0 ^^ s 1 ^^ s 2)
    · have hcc : (∑ j : Fin 3, (if s j ≠ k j then (1:ℂ) else 0)) = 2 := by
        have hcc' : (∑ j : Fin 3, (if s j ≠ k j then (1:ℂ) else 0))
            = ((Finset.univ.filter (fun j : Fin 3 => s j ≠ k j)).card : ℂ) := by
          rw [Finset.card_filter]
          push_cast
          apply Finset.sum_congr rfl; intro j _
          by_cases h : s j ≠ k j <;> simp [h]
        rw [hcc', magic_square_even_diff_card_two s k hbool hk hs]
        norm_num
      rw [hcc, if_neg hs]
    · have hA0 : A 0 s = 0 := hA_even 0 s hbool
      rw [if_neg hs, hA0]
      simp

private lemma msd_sum_ite_A {dA : ℕ}
    (A : Fin 3 → (Fin 3 → Bool) → Matrix (Fin dA) (Fin dA) ℂ)
    (k : Fin 3 → Bool) (hA : (∑ s, A 0 s) = 1) :
    (∑ s : Fin 3 → Bool, (if s = k then (0:Matrix (Fin dA) (Fin dA) ℂ) else A 0 s)) = 1 - A 0 k := by
  have hpt : ∀ s, (if s = k then (0:Matrix (Fin dA) (Fin dA) ℂ) else A 0 s)
      = A 0 s - (if s = k then A 0 s else 0) := by
    intro s; by_cases h : s = k <;> simp [h]
  simp only [hpt]
  rw [Finset.sum_sub_distrib]
  rw [Finset.sum_ite_eq']
  simp [hA]

private lemma msd_R_csum {dA dB : ℕ}
    (A : Fin 3 → (Fin 3 → Bool) → Matrix (Fin dA) (Fin dA) ℂ)
    (B : Fin 3 → (Fin 3 → Bool) → Matrix (Fin dB) (Fin dB) ℂ)
    (k : Fin 3 → Bool) (hB : ∀ j, (∑ c, B j c) = 1) (j : Fin 3) (s : Fin 3 → Bool) :
    (∑ c, ((if s j ≠ k j then (1:ℂ) else 0) • (A 0 s ⊗ₖ B j c)))
    = (if s j ≠ k j then (1:ℂ) else 0) • (A 0 s ⊗ₖ (1:Matrix (Fin dB) (Fin dB) ℂ)) := by
  rw [← Finset.smul_sum]
  rw [← msd_finset_sum_kronecker_right]
  rw [hB j]

private lemma msd_R_jsum {dA dB : ℕ}
    (A : Fin 3 → (Fin 3 → Bool) → Matrix (Fin dA) (Fin dA) ℂ)
    (B : Fin 3 → (Fin 3 → Bool) → Matrix (Fin dB) (Fin dB) ℂ)
    (k : Fin 3 → Bool) (hB : ∀ j, (∑ c, B j c) = 1) (s : Fin 3 → Bool) :
    (∑ j, ∑ c, ((if s j ≠ k j then (1:ℂ) else 0) • (A 0 s ⊗ₖ B j c)))
    = (∑ j, (if s j ≠ k j then (1:ℂ) else 0)) • (A 0 s ⊗ₖ (1:Matrix (Fin dB) (Fin dB) ℂ)) := by
  trans (∑ j, ((if s j ≠ k j then (1:ℂ) else 0) • (A 0 s ⊗ₖ (1:Matrix (Fin dB) (Fin dB) ℂ))))
  · apply Finset.sum_congr rfl; intro j _
    exact msd_R_csum A B k hB j s
  · rw [← Finset.sum_smul]

private lemma msd_R {dA dB : ℕ}
    (A : Fin 3 → (Fin 3 → Bool) → Matrix (Fin dA) (Fin dA) ℂ)
    (B : Fin 3 → (Fin 3 → Bool) → Matrix (Fin dB) (Fin dB) ℂ)
    (k : Fin 3 → Bool)
    (hA_povm : ∀ x, is_povm dA (A x))
    (hA_even : ∀ x s, (s 0 ^^ s 1 ^^ s 2) = true → A x s = 0)
    (hB_povm : ∀ j, is_povm dB (B j))
    (hk : (k 0 ^^ k 1 ^^ k 2) = false) :
    (∑ j, ∑ s, ∑ c, ((if s j ≠ k j then (1:ℂ) else 0) • (A 0 s ⊗ₖ B j c)))
    = (2:ℂ) • ((1 - A 0 k) ⊗ₖ (1:Matrix (Fin dB) (Fin dB) ℂ)) := by
  have hB : ∀ j, (∑ c, B j c) = 1 := fun j => (hB_povm j).2
  have hA : (∑ s, A 0 s) = 1 := (hA_povm 0).2
  rw [Finset.sum_comm]
  trans (∑ s, (∑ j, (if s j ≠ k j then (1:ℂ) else 0)) • (A 0 s ⊗ₖ (1:Matrix (Fin dB) (Fin dB) ℂ)))
  · apply Finset.sum_congr rfl; intro s _
    exact msd_R_jsum A B k hB s
  trans (∑ s, (((∑ j, (if s j ≠ k j then (1:ℂ) else 0)) • (A 0 s)) ⊗ₖ (1:Matrix (Fin dB) (Fin dB) ℂ)))
  · apply Finset.sum_congr rfl; intro s _
    rw [← Matrix.smul_kronecker]
  trans (∑ s, (((2:ℂ) • (if s = k then (0:Matrix (Fin dA) (Fin dA) ℂ) else A 0 s)) ⊗ₖ (1:Matrix (Fin dB) (Fin dB) ℂ)))
  · apply Finset.sum_congr rfl; intro s _
    rw [msd_coeff_smul A k hA_even hk s]
  trans (∑ s, (2:ℂ) • ((if s = k then (0:Matrix (Fin dA) (Fin dA) ℂ) else A 0 s) ⊗ₖ (1:Matrix (Fin dB) (Fin dB) ℂ)))
  · apply Finset.sum_congr rfl; intro s _
    rw [Matrix.smul_kronecker]
  trans ((2:ℂ) • (∑ s, ((if s = k then (0:Matrix (Fin dA) (Fin dA) ℂ) else A 0 s) ⊗ₖ (1:Matrix (Fin dB) (Fin dB) ℂ))))
  · rw [Finset.smul_sum]
  trans ((2:ℂ) • ((∑ s, (if s = k then (0:Matrix (Fin dA) (Fin dA) ℂ) else A 0 s)) ⊗ₖ (1:Matrix (Fin dB) (Fin dB) ℂ)))
  · rw [msd_finset_sum_kronecker]
  rw [msd_sum_ite_A A k hA]

private lemma msd_key {dA dB : ℕ}
    (A : Fin 3 → (Fin 3 → Bool) → Matrix (Fin dA) (Fin dA) ℂ)
    (B : Fin 3 → (Fin 3 → Bool) → Matrix (Fin dB) (Fin dB) ℂ)
    (k : Fin 3 → Bool)
    (hA_povm : ∀ x, is_povm dA (A x))
    (hA_even : ∀ x s, (s 0 ^^ s 1 ^^ s 2) = true → A x s = 0)
    (hB_povm : ∀ j, is_povm dB (B j))
    (hk : (k 0 ^^ k 1 ^^ k 2) = false) :
    (2 / 9 : ℂ) • (((1 : Matrix (Fin dA) (Fin dA) ℂ) - A 0 k) ⊗ₖ (1 : Matrix (Fin dB) (Fin dB) ℂ))
      - (magic_square_winning_op A B - magic_square_winning_op_det_row0 A B k)
    = (1/9 : ℂ) • ∑ j, ∑ s, ∑ c, (((if s j ≠ k j then (1:ℂ) else 0) -
        ((if s j = c 0 then (1:ℂ) else 0) - (if k j = c 0 then (1:ℂ) else 0))) • (A 0 s ⊗ₖ B j c)) := by
  have hW := msd_W_sub_Wd_eq A B k
  have hR := msd_R A B k hA_povm hA_even hB_povm hk
  have hL1 := msd_L1 A B k
  have hL2 := msd_L2 A B k hA_povm
  have hS_eq : (∑ j, ∑ s, ∑ c, (if s j = c 0 then ((A 0 s - (if s = k then (1:Matrix (Fin dA) (Fin dA) ℂ) else 0)) ⊗ₖ B j c) else 0))
      = ∑ j, ∑ s, ∑ c, (((if s j = c 0 then (1:ℂ) else 0) - (if k j = c 0 then (1:ℂ) else 0)) • (A 0 s ⊗ₖ B j c)) :=
    hL1.trans hL2.symm
  have hTY : (2 / 9 : ℂ) • (((1 : Matrix (Fin dA) (Fin dA) ℂ) - A 0 k) ⊗ₖ (1 : Matrix (Fin dB) (Fin dB) ℂ))
      = (1/9 : ℂ) • (∑ j, ∑ s, ∑ c, ((if s j ≠ k j then (1:ℂ) else 0) • (A 0 s ⊗ₖ B j c))) := by
    rw [hR, smul_smul]; norm_num
  have hstep1 : (1/9 : ℂ) • (∑ j, ∑ s, ∑ c, ((if s j ≠ k j then (1:ℂ) else 0) • (A 0 s ⊗ₖ B j c)))
      - (1/9 : ℂ) • (∑ j, ∑ s, ∑ c, (if s j = c 0 then ((A 0 s - (if s = k then (1:Matrix (Fin dA) (Fin dA) ℂ) else 0)) ⊗ₖ B j c) else 0))
      = (1/9 : ℂ) • ((∑ j, ∑ s, ∑ c, ((if s j ≠ k j then (1:ℂ) else 0) • (A 0 s ⊗ₖ B j c)))
        - (∑ j, ∑ s, ∑ c, (if s j = c 0 then ((A 0 s - (if s = k then (1:Matrix (Fin dA) (Fin dA) ℂ) else 0)) ⊗ₖ B j c) else 0))) := by
    rw [smul_sub]
  have hstep2 : (∑ j, ∑ s, ∑ c, ((if s j ≠ k j then (1:ℂ) else 0) • (A 0 s ⊗ₖ B j c)))
        - (∑ j, ∑ s, ∑ c, (if s j = c 0 then ((A 0 s - (if s = k then (1:Matrix (Fin dA) (Fin dA) ℂ) else 0)) ⊗ₖ B j c) else 0))
      = (∑ j, ∑ s, ∑ c, ((if s j ≠ k j then (1:ℂ) else 0) • (A 0 s ⊗ₖ B j c)))
        - (∑ j, ∑ s, ∑ c, (((if s j = c 0 then (1:ℂ) else 0) - (if k j = c 0 then (1:ℂ) else 0)) • (A 0 s ⊗ₖ B j c))) := by
    rw [hS_eq]
  have hstep3 : (∑ j, ∑ s, ∑ c, ((if s j ≠ k j then (1:ℂ) else 0) • (A 0 s ⊗ₖ B j c)))
        - (∑ j, ∑ s, ∑ c, (((if s j = c 0 then (1:ℂ) else 0) - (if k j = c 0 then (1:ℂ) else 0)) • (A 0 s ⊗ₖ B j c)))
      = ∑ j, ∑ s, ∑ c, (((if s j ≠ k j then (1:ℂ) else 0) • (A 0 s ⊗ₖ B j c))
        - (((if s j = c 0 then (1:ℂ) else 0) - (if k j = c 0 then (1:ℂ) else 0)) • (A 0 s ⊗ₖ B j c))) :=
    msd_sum_sub_sum _ _
  rw [hTY, hW, hstep1, hstep2, hstep3]
  congr 1
  apply Finset.sum_congr rfl; intro j _
  apply Finset.sum_congr rfl; intro s _
  apply Finset.sum_congr rfl; intro c _
  rw [← sub_smul]

/-- The difference W - W^(k) is bounded in the Loewner order by (2/9)(I - A_{k|0}) ⊗ I. -/
theorem magic_square_winning_op_sub_det_row0_le {dA dB : ℕ}
    (A : Fin 3 → (Fin 3 → Bool) → Matrix (Fin dA) (Fin dA) ℂ)
    (B : Fin 3 → (Fin 3 → Bool) → Matrix (Fin dB) (Fin dB) ℂ)
    (k : Fin 3 → Bool)
    (hA_povm : ∀ x, is_povm dA (A x))
    (hA_even : ∀ x s, xor (xor (s 0) (s 1)) (s 2) = true → A x s = 0)
    (hB_povm : ∀ j, is_povm dB (B j))
    (hB_odd : ∀ j c, xor (xor (c 0) (c 1)) (c 2) = false → B j c = 0)
    (hk : xor (xor (k 0) (k 1)) (k 2) = false) :
    open scoped ComplexOrder MatrixOrder Kronecker in
    magic_square_winning_op A B - magic_square_winning_op_det_row0 A B k ≤
      (2 / 9 : ℂ) • (((1 : Matrix (Fin dA) (Fin dA) ℂ) - A 0 k) ⊗ₖ (1 : Matrix (Fin dB) (Fin dB) ℂ)) := by
  rw [Matrix.le_iff]
  exact (msd_key A B k hA_povm hA_even hB_povm hk) ▸
    Matrix.PosSemidef.smul (msd_coeff_psd A B k hA_povm hB_povm) (by simp)
