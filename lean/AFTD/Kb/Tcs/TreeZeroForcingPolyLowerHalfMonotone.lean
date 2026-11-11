import AFTD.Prelude
import AFTD.Kb.Tcs.ZeroForcingPoly
import AFTD.Kb.Tcs.IsZeroForcingSet
import AFTD.Kb.Tcs.ZeroForced

/-!
# tree_zero_forcing_poly_lower_half_monotone

Topic: graphs   Node: 58dc030f5711

Provenance: formalization of a published result. Source: arXiv:2611.11352 Sec. 1

For any finite tree $T$ on a finite vertex set $V$, the coefficient of $X^i$ in the zero forcing polynomial of $T$ is less than or equal to the coefficient of $X^{i+1}$ for every integer $i$ satisfying $1 \le i < \lfloor (|V| + 1) / 2 \rfloor$ (i.e., using integer division).
-/

open scoped Classical
open Polynomial

theorem tree_zero_forcing_poly_lower_half_monotone_zero_forced_mono {V : Type*} (G : SimpleGraph V) {S S' : Set V}
    (h : S ⊆ S') {v : V} (hv : ZeroForced G S v) : ZeroForced G S' v := by
  induction hv with
  | init x hx => exact ZeroForced.init x (h hx)
  | step u w hu hadj hx ihu ihx =>
    exact ZeroForced.step u w ihu hadj ihx

theorem tree_zero_forcing_poly_lower_half_monotone_is_zero_forcing_set_mono {V : Type*} (G : SimpleGraph V) {S S' : Set V}
    (h : S ⊆ S') (hS : is_zero_forcing_set G S) : is_zero_forcing_set G S' :=
  fun v => tree_zero_forcing_poly_lower_half_monotone_zero_forced_mono G h (hS v)

lemma tree_zero_forcing_poly_lower_half_monotone_coeff_eq_card_filter {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ) :
    (zero_forcing_poly G).coeff k =
      ((Finset.powersetCard k (Finset.univ : Finset V)).filter
        (fun (S : Finset V) => is_zero_forcing_set G (S : Set V))).card := by
  dsimp [zero_forcing_poly]
  rw [finsetSum_coeff]
  simp_rw [apply_ite (fun p : Polynomial ℕ => coeff p k), coeff_zero, coeff_X_pow]
  let A : Finset (Finset V) := (Finset.powersetCard k (Finset.univ : Finset V)).filter
        (fun (S : Finset V) => is_zero_forcing_set G (S : Set V))
  have hA : ∀ S ∈ A, (if is_zero_forcing_set G (S : Set V) then if k = S.card then 1 else 0 else 0) = (1 : ℕ) := by
    intro S hS
    have hS' : S ∈ Finset.powersetCard k (Finset.univ : Finset V) ∧ is_zero_forcing_set G (S : Set V) :=
      Finset.mem_filter.mp hS
    rw [Finset.mem_powersetCard_univ] at hS'
    rw [if_pos hS'.2, if_pos hS'.1.symm]
  have hAc : ∀ S ∈ (Finset.univ : Finset (Finset V)), S ∉ A →
      (if is_zero_forcing_set G (S : Set V) then if k = S.card then 1 else 0 else 0) = (0 : ℕ) := by
    intro S _ hS
    have hS' : ¬ (S ∈ Finset.powersetCard k (Finset.univ : Finset V) ∧ is_zero_forcing_set G (S : Set V)) :=
      fun h => hS (Finset.mem_filter.mpr h)
    rw [Finset.mem_powersetCard_univ] at hS'
    by_cases hzf : is_zero_forcing_set G (S : Set V)
    · rw [if_pos hzf]
      have : ¬ k = S.card := fun hk => hS' ⟨hk.symm, hzf⟩
      rw [if_neg this]
    · rw [if_neg hzf]
  rw [Finset.card_eq_sum_ones]
  change (∑ x : Finset V, _) = ∑ x ∈ A, 1
  rw [Finset.sum_congr rfl (fun S hS => (hA S hS).symm)]
  exact (Finset.sum_subset (Finset.subset_univ A) (fun S hS hS_not => hAc S hS hS_not)).symm

lemma tree_zero_forcing_poly_lower_half_monotone_card_filter_powersetCard_succ {V : Type*} [Fintype V] (s : Finset V) (i : ℕ)
    (hs : s.card = i) :
    ((Finset.powersetCard (i + 1) (Finset.univ : Finset V)).filter (fun x => s ⊆ x)).card =
      Fintype.card V - i := by
  have hsub : s ⊆ Finset.univ := Finset.subset_univ s
  have hle : s.card ≤ i + 1 := hs ▸ Nat.le_succ i
  have := Finset.card_filter_powersetCard_subset s Finset.univ (i + 1) hsub hle
  rw [hs, Finset.card_univ] at this
  have h1 : i + 1 - i = 1 := by omega
  rw [h1, Nat.choose_one_right] at this
  exact this

lemma tree_zero_forcing_poly_lower_half_monotone_filter_B_eq_filter_powersetCard {V : Type*} [Fintype V] (G : SimpleGraph V)
    (i : ℕ) (s : Finset V) (hsA : is_zero_forcing_set G (s : Set V)) :
    ((Finset.powersetCard (i + 1) (Finset.univ : Finset V)).filter
        (fun (x : Finset V) => is_zero_forcing_set G (x : Set V))).filter (fun x => s ⊆ x) =
      (Finset.powersetCard (i + 1) (Finset.univ : Finset V)).filter (fun x => s ⊆ x) := by
  ext x
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨⟨hx_pow, _⟩, hsx⟩
    exact ⟨hx_pow, hsx⟩
  · rintro ⟨hx_pow, hsx⟩
    have hsub : (s : Set V) ⊆ (x : Set V) := Finset.coe_subset.mpr hsx
    exact ⟨⟨hx_pow, tree_zero_forcing_poly_lower_half_monotone_is_zero_forcing_set_mono G hsub hsA⟩, hsx⟩

lemma tree_zero_forcing_poly_lower_half_monotone_card_filter_A_sub {V : Type*} [Fintype V] (G : SimpleGraph V) (x : Finset V) (i : ℕ)
    (hx : x.card = i + 1) :
    (((Finset.powersetCard i (Finset.univ : Finset V)).filter
        (fun (s : Finset V) => is_zero_forcing_set G (s : Set V))).filter (fun s => s ⊆ x)).card ≤ i + 1 := by
  have hsub : ((Finset.powersetCard i (Finset.univ : Finset V)).filter
        (fun (s : Finset V) => is_zero_forcing_set G (s : Set V))).filter (fun s => s ⊆ x) ⊆
      (Finset.powersetCard i (Finset.univ : Finset V)).filter (fun s => s ⊆ x) := by
    intro s hs
    simp only [Finset.mem_filter] at hs ⊢
    exact ⟨hs.1.1, hs.2⟩
  apply le_trans (Finset.card_le_card hsub)
  have heq : (Finset.powersetCard i (Finset.univ : Finset V)).filter (fun s => s ⊆ x) =
      Finset.powersetCard i x := by
    ext s
    simp only [Finset.mem_filter, Finset.mem_powersetCard, Finset.subset_univ, true_and]
    tauto
  rw [heq, Finset.card_powersetCard, hx, Nat.choose_succ_self_right]

/-- The lower half of the coefficients of the zero forcing polynomial of any finite tree is non-decreasing. -/
theorem tree_zero_forcing_poly_lower_half_monotone
    {V : Type*} [Fintype V] (T : SimpleGraph V) (hT : T.IsTree)
    (i : ℕ) (hi1 : 1 ≤ i) (hi2 : i < (Fintype.card V + 1) / 2) :
    (zero_forcing_poly T).coeff i ≤ (zero_forcing_poly T).coeff (i + 1) := by
  rw [tree_zero_forcing_poly_lower_half_monotone_coeff_eq_card_filter T i,
      tree_zero_forcing_poly_lower_half_monotone_coeff_eq_card_filter T (i + 1)]
  let A := (Finset.powersetCard i (Finset.univ : Finset V)).filter
      (fun (s : Finset V) => is_zero_forcing_set T (s : Set V))
  let B := (Finset.powersetCard (i + 1) (Finset.univ : Finset V)).filter
      (fun (x : Finset V) => is_zero_forcing_set T (x : Set V))
  have h_sum : ∑ s ∈ A, (B.filter (fun x => s ⊆ x)).card =
      ∑ x ∈ B, (A.filter (fun s => s ⊆ x)).card := by
    simp_rw [Finset.card_filter]
    exact Finset.sum_comm
  have h_left : ∑ s ∈ A, (B.filter (fun x => s ⊆ x)).card = A.card * (Fintype.card V - i) := by
    have h_each : ∀ s ∈ A, (B.filter (fun x => s ⊆ x)).card = Fintype.card V - i := by
      intro s hs
      have hs' : s ∈ Finset.powersetCard i (Finset.univ : Finset V) ∧ is_zero_forcing_set T (s : Set V) :=
        Finset.mem_filter.mp hs
      rw [Finset.mem_powersetCard_univ] at hs'
      have heq : B.filter (fun x => s ⊆ x) =
          (Finset.powersetCard (i + 1) (Finset.univ : Finset V)).filter (fun x => s ⊆ x) :=
        tree_zero_forcing_poly_lower_half_monotone_filter_B_eq_filter_powersetCard T i s hs'.2
      rw [heq]
      exact tree_zero_forcing_poly_lower_half_monotone_card_filter_powersetCard_succ s i hs'.1
    rw [Finset.sum_congr rfl h_each]
    simp only [Finset.sum_const, smul_eq_mul]
  have h_right : ∑ x ∈ B, (A.filter (fun s => s ⊆ x)).card ≤ B.card * (i + 1) := by
    have h_each : ∀ x ∈ B, (A.filter (fun s => s ⊆ x)).card ≤ i + 1 := by
      intro x hx
      have hx' : x ∈ Finset.powersetCard (i + 1) (Finset.univ : Finset V) ∧ is_zero_forcing_set T (x : Set V) :=
        Finset.mem_filter.mp hx
      rw [Finset.mem_powersetCard_univ] at hx'
      exact tree_zero_forcing_poly_lower_half_monotone_card_filter_A_sub T x i hx'.1
    have := Finset.sum_le_card_nsmul B (fun x => (A.filter (fun s => s ⊆ x)).card) (i + 1) h_each
    rwa [nsmul_eq_mul] at this
  have h_mul : A.card * (Fintype.card V - i) ≤ B.card * (i + 1) := by
    rw [← h_left, h_sum]
    exact h_right
  have hle : i + 1 ≤ Fintype.card V - i := by omega
  have h1 : A.card * (i + 1) ≤ A.card * (Fintype.card V - i) := Nat.mul_le_mul_left A.card hle
  have h2 : A.card * (i + 1) ≤ B.card * (i + 1) := le_trans h1 h_mul
  exact Nat.le_of_mul_le_mul_right h2 (by omega)
