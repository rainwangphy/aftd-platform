import AFTD.Prelude
import AFTD.Kb.Tcs.SprOpt
import AFTD.Kb.Tcs.SprSignCount
import AFTD.Kb.Tcs.SprValue
import AFTD.Kb.Tcs.SprMove

/-!
# spr_opt_capacity_le

Topic: learning   Node: d0d4cec8673a

Provenance: original. Related work: arXiv:2410.07623 (Explicit asymptotic bounds for sequential calibration beyond T^{2/3})

For every integer k ≥ 1, board size n ∈ {2k - 1, 2k}, and horizon t, the sign-preservation-with-reuse minimax value satisfies spr_opt n t ≤ k.
-/

open Finset

def spr_opt_capacity_le_inv (n : ℕ) (b : Fin n → Option Bool) : Prop :=
  (∀ i : Fin n, b i = none ∨ b i = some (decide ((i : ℕ) % 2 = 1))) ∧
  (∀ i₁ i₂ : Fin n, (b i₁).isSome → (b i₂).isSome → (i₁ : ℕ) / 2 = (i₂ : ℕ) / 2 → i₁ = i₂)

lemma spr_opt_capacity_le_inv_none (n : ℕ) : spr_opt_capacity_le_inv n (fun _ => none) :=
  ⟨fun _ => Or.inl rfl, fun _ _ h₁ => by simp at h₁⟩

lemma spr_opt_capacity_le_div_two_eq_cases {i j : ℕ} (hdiv : i / 2 = j / 2) (hne : i ≠ j) :
    (i < j ∧ i % 2 = 0 ∧ j % 2 = 1) ∨ (j < i ∧ j % 2 = 0 ∧ i % 2 = 1) := by
  have hi := Nat.div_add_mod i 2
  have hj := Nat.div_add_mod j 2
  have hmi : i % 2 < 2 := Nat.mod_lt i (by decide)
  have hmj : j % 2 < 2 := Nat.mod_lt j (by decide)
  omega

lemma spr_opt_capacity_le_legal_move {n : ℕ} (b : Fin n → Option Bool) (j : Fin n) (hj : b j = none)
    (hinv : spr_opt_capacity_le_inv n b) :
    let R : Finset (Fin n) := univ.filter (fun i => (i : ℕ) / 2 = (j : ℕ) / 2 ∧ (b i).isSome)
    ∀ i ∈ R, (i < j ∧ b i = some false) ∨ (j < i ∧ b i = some true) := by
  intro R i hi
  simp only [R, mem_filter, mem_univ, true_and] at hi
  have hne : (i : ℕ) ≠ (j : ℕ) := by
    intro heq
    have : i = j := Fin.ext heq
    have hbs := hi.2
    rw [this, hj] at hbs
    contradiction
  have hcases := spr_opt_capacity_le_div_two_eq_cases hi.1 hne
  have hbi : b i = some (decide ((i : ℕ) % 2 = 1)) := by
    rcases hinv.1 i with h | h
    · have := hi.2; simp [h] at this
    · exact h
  rcases hcases with ⟨hlt, hmod, _⟩ | ⟨hlt, _, hmod⟩
  · left
    refine ⟨Fin.lt_def.2 hlt, ?_⟩
    rw [hbi, show decide ((i : ℕ) % 2 = 1) = false by simp [hmod]]
  · right
    refine ⟨Fin.lt_def.2 hlt, ?_⟩
    rw [hbi, show decide ((i : ℕ) % 2 = 1) = true by simp [hmod]]

lemma spr_opt_capacity_le_inv_move {n : ℕ} (b : Fin n → Option Bool) (j : Fin n)
    (hinv : spr_opt_capacity_le_inv n b) :
    let R : Finset (Fin n) := univ.filter (fun i => (i : ℕ) / 2 = (j : ℕ) / 2 ∧ (b i).isSome)
    let s : Bool := decide ((j : ℕ) % 2 = 1)
    spr_opt_capacity_le_inv n (spr_move b j R s) := by
  dsimp
  set R : Finset (Fin n) := univ.filter (fun i => (i : ℕ) / 2 = (j : ℕ) / 2 ∧ (b i).isSome)
  set s : Bool := decide ((j : ℕ) % 2 = 1)
  obtain ⟨h_parity, hinj⟩ := hinv
  constructor
  · intro i
    simp only [spr_move]
    split_ifs with h1 h2
    · rw [h1]; right; rfl
    · left; rfl
    · exact h_parity i
  · intro i₁ i₂ h₁ h₂ hdiv
    simp only [spr_move] at h₁ h₂
    by_cases h1 : i₁ = j
    · by_cases h2 : i₂ = j
      · rw [h1, h2]
      · exfalso
        simp only [if_neg h2] at h₂
        split_ifs at h₂ with hR
        · contradiction
        have h_in_R : i₂ ∈ R := by
          simp only [R, mem_filter, mem_univ, true_and]
          exact ⟨by rw [← hdiv, h1], h₂⟩
        exact hR h_in_R
    · by_cases h2 : i₂ = j
      · exfalso
        simp only [if_neg h1] at h₁
        split_ifs at h₁ with hR
        · contradiction
        have h_in_R : i₁ ∈ R := by
          simp only [R, mem_filter, mem_univ, true_and]
          exact ⟨by rw [hdiv, h2], h₁⟩
        exact hR h_in_R
      · simp only [if_neg h1] at h₁
        simp only [if_neg h2] at h₂
        split_ifs at h₁ with hR1
        · contradiction
        split_ifs at h₂ with hR2
        · contradiction
        exact hinj i₁ i₂ h₁ h₂ hdiv

lemma spr_opt_capacity_le_sign_count_le_of_inv {n k : ℕ} (hn : n ≤ 2 * k) (b : Fin n → Option Bool)
    (hinv : spr_opt_capacity_le_inv n b) : spr_sign_count b ≤ k := by
  have h_maps : Set.MapsTo (fun i : Fin n => (i : ℕ) / 2)
      ↑(univ.filter fun i : Fin n => (b i).isSome) ↑(range k) := by
    intro i hi
    simp only [mem_coe, mem_filter, mem_univ, true_and] at hi
    simp only [mem_coe, mem_range]
    have : (i : ℕ) < 2 * k := lt_of_lt_of_le i.isLt hn
    exact Nat.div_lt_of_lt_mul this
  have h_inj : Set.InjOn (fun i : Fin n => (i : ℕ) / 2) ↑(univ.filter fun i : Fin n => (b i).isSome) := by
    intro i₁ h₁ i₂ h₂ heq
    simp only [mem_coe, mem_filter, mem_univ, true_and] at h₁ h₂
    exact hinv.2 i₁ i₂ h₁ h₂ heq
  have h := Finset.card_le_card_of_injOn (fun i : Fin n => (i : ℕ) / 2) h_maps h_inj
  rw [card_range] at h
  exact h

lemma spr_opt_capacity_le_value_le_of_inv {n k : ℕ} (hn : n ≤ 2 * k) (t : ℕ) (b : Fin n → Option Bool)
    (hinv : spr_opt_capacity_le_inv n b) : spr_value n t b ≤ k := by
  induction t generalizing b with
  | zero =>
    rw [spr_value.eq_1]
    exact spr_opt_capacity_le_sign_count_le_of_inv hn b hinv
  | succ r ih =>
    rw [spr_value.eq_2]
    apply Nat.max_le.2
    refine ⟨spr_opt_capacity_le_sign_count_le_of_inv hn b hinv, ?_⟩
    apply Finset.sup_le
    intro j hj
    have hj_none : b j = none := (Finset.mem_filter.1 hj).2
    let R : Finset (Fin n) := univ.filter (fun i => (i : ℕ) / 2 = (j : ℕ) / 2 ∧ (b i).isSome)
    let s : Bool := decide ((j : ℕ) % 2 = 1)
    have hp_mem : (R, s) ∈ (Finset.univ : Finset (Finset (Fin n) × Bool)).filter
        fun p => ∀ i ∈ p.1, (i < j ∧ b i = some false) ∨ (j < i ∧ b i = some true) := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_univ _, spr_opt_capacity_le_legal_move b j hj_none hinv⟩
    have h_next : spr_opt_capacity_le_inv n (spr_move b j R s) := spr_opt_capacity_le_inv_move b j hinv
    exact le_trans (Finset.inf'_le _ hp_mem) (ih (spr_move b j R s) h_next)

/-- The capacity ceiling for sign preservation with reuse on linear boards: on boards of size 2k - 1 and 2k, the minimax value never exceeds k. -/
theorem spr_opt_capacity_le
    (k : ℕ) (hk : 1 ≤ k) (n : ℕ) (hn : n = 2 * k - 1 ∨ n = 2 * k) (t : ℕ) :
    spr_opt n t ≤ k := by
  have _ := hk
  have hn_le : n ≤ 2 * k := by
    rcases hn with rfl | rfl
    · exact Nat.sub_le (2 * k) 1
    · exact le_rfl
  exact spr_opt_capacity_le_value_le_of_inv hn_le t (fun _ => none) (spr_opt_capacity_le_inv_none n)
