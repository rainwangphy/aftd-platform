import AFTD.Prelude
import AFTD.Kb.Tcs.ZeroForcingPoly
import AFTD.Kb.Tcs.PolynomialIsUnimodal
import AFTD.Kb.Tcs.TreeZeroForcingPolyLowerHalfMonotone
import AFTD.Kb.Tcs.ZeroForced
import AFTD.Kb.Tcs.IsZeroForcingSet

/-!
# star_graph_zero_forcing_poly_unimodal

Topic: graphs   Node: 4af7631ae7b9

Provenance: formalization of a published result. Source: arXiv:2611.11352 Sec. 1

For every natural number n, the complete bipartite graph K_{1, n} on Unit ⊕ Fin n has a unimodal zero forcing polynomial.
-/

open scoped Classical
open Polynomial

lemma star_missing_two (n : ℕ) (S : Set (Unit ⊕ Fin n))
    (j k : Fin n) (hjk : j ≠ k)
    (hj : Sum.inr j ∉ S) (hk : Sum.inr k ∉ S) :
    ∀ v, ZeroForced (completeBipartiteGraph Unit (Fin n)) S v →
      v ≠ Sum.inr j ∧ v ≠ Sum.inr k := by
  intro v hv
  induction hv with
  | init v hv =>
    constructor <;> intro h <;> subst v
    · exact hj hv
    · exact hk hv
  | step u w hu hadj hother ihu ihother =>
    constructor
    · intro hw
      subst w
      cases u with
      | inl a =>
        have h := ihother (Sum.inr k) (by simp [completeBipartiteGraph]) (by simpa using hjk.symm)
        exact h.2 rfl
      | inr a => simp [completeBipartiteGraph] at hadj
    · intro hw
      subst w
      cases u with
      | inl a =>
        have h := ihother (Sum.inr j) (by simp [completeBipartiteGraph]) (by simpa using hjk)
        exact h.1 rfl
      | inr a => simp [completeBipartiteGraph] at hadj


lemma star_zfs_card_lower (n : ℕ) (S : Finset (Unit ⊕ Fin n))
    (hz : is_zero_forcing_set (completeBipartiteGraph Unit (Fin n)) (S : Set (Unit ⊕ Fin n))) : n ≤ S.card + 1 := by
  let M : Finset (Fin n) := Finset.univ.filter (fun j => Sum.inr j ∉ S)
  have hM : M.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro j hj k hk
    by_contra hne
    have hj' : Sum.inr j ∉ S := (Finset.mem_filter.mp hj).2
    have hk' : Sum.inr k ∉ S := (Finset.mem_filter.mp hk).2
    exact (star_missing_two n S j k hne hj' hk' _ (hz (Sum.inr j))).1 rfl
  let L : Finset (Unit ⊕ Fin n) := Finset.univ.image Sum.inr
  let U : Finset (Unit ⊕ Fin n) := M.image Sum.inr
  have hL : L.card = n := by
    simp [L, Finset.card_image_of_injective _ Sum.inr_injective]
  have hU : U.card ≤ 1 := le_trans (Finset.card_image_le) hM
  have hsub : L ⊆ S ∪ U := by
    intro x hx
    simp only [L, Finset.mem_image, Finset.mem_univ, true_and] at hx
    obtain ⟨j, rfl⟩ := hx
    by_cases h : Sum.inr j ∈ S
    · exact Finset.mem_union_left U h
    · apply Finset.mem_union_right
      exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, rfl⟩
  have hc := Finset.card_le_card hsub
  have hc' := Finset.card_union_le S U
  omega

lemma star_coeff_low_zero (n k : ℕ) (hk : k + 2 ≤ n) :
    (zero_forcing_poly (completeBipartiteGraph Unit (Fin n))).coeff k = 0 := by
  rw [tree_zero_forcing_poly_lower_half_monotone_coeff_eq_card_filter]
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro S hS
  have hS' := Finset.mem_filter.mp hS
  have hcard := Finset.mem_powersetCard_univ.mp hS'.1
  have hlower := star_zfs_card_lower n S hS'.2
  omega

lemma star_no_center (n : ℕ) (S : Finset (Unit ⊕ Fin n))
    (hcard : S.card + 1 = n)
    (hz : is_zero_forcing_set (completeBipartiteGraph Unit (Fin n)) (S : Set (Unit ⊕ Fin n))) :
    Sum.inl () ∉ S := by
  intro hc
  let M : Finset (Fin n) := Finset.univ.filter (fun j => Sum.inr j ∉ S)
  have hM : M.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro j hj k hk
    by_contra hne
    have hj' : Sum.inr j ∉ S := (Finset.mem_filter.mp hj).2
    have hk' : Sum.inr k ∉ S := (Finset.mem_filter.mp hk).2
    exact (star_missing_two n S j k hne hj' hk' _ (hz (Sum.inr j))).1 rfl
  let U : Finset (Unit ⊕ Fin n) := M.image Sum.inr
  have hU : U.card ≤ 1 := le_trans Finset.card_image_le hM
  have hsub : (Finset.univ : Finset (Unit ⊕ Fin n)) ⊆ S ∪ U := by
    intro x hx
    cases x with
    | inl a => cases a; exact Finset.mem_union_left U hc
    | inr j =>
      by_cases h : Sum.inr j ∈ S
      · exact Finset.mem_union_left U h
      · apply Finset.mem_union_right
        exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ _, h⟩, rfl⟩
  have hv := Finset.card_le_card hsub
  have hv' := Finset.card_union_le S U
  simp only [Finset.card_univ, Fintype.card_sum, Fintype.card_unit, Fintype.card_fin] at hv
  omega

lemma star_coeff_penult_le (n : ℕ) (hn : 1 ≤ n) :
    (zero_forcing_poly (completeBipartiteGraph Unit (Fin n))).coeff (n-1) ≤
      (zero_forcing_poly (completeBipartiteGraph Unit (Fin n))).coeff n := by
  rw [tree_zero_forcing_poly_lower_half_monotone_coeff_eq_card_filter,
      tree_zero_forcing_poly_lower_half_monotone_coeff_eq_card_filter]
  let G := completeBipartiteGraph Unit (Fin n)
  let A := (Finset.powersetCard (n-1) (Finset.univ : Finset (Unit ⊕ Fin n))).filter
    (fun (S : Finset (Unit ⊕ Fin n)) => is_zero_forcing_set G (S : Set (Unit ⊕ Fin n)))
  let B := (Finset.powersetCard n (Finset.univ : Finset (Unit ⊕ Fin n))).filter
    (fun (S : Finset (Unit ⊕ Fin n)) => is_zero_forcing_set G (S : Set (Unit ⊕ Fin n)))
  change A.card ≤ B.card
  apply Finset.card_le_card_of_injOn (fun S => insert (Sum.inl ()) S)
  · intro S hS
    have hS' := Finset.mem_filter.mp hS
    have hcard := Finset.mem_powersetCard_univ.mp hS'.1
    have hcenter : Sum.inl () ∉ S := star_no_center n S (by omega) hS'.2
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_powersetCard_univ.mpr
      rw [Finset.card_insert_of_notMem hcenter, hcard]
      omega
    · apply tree_zero_forcing_poly_lower_half_monotone_is_zero_forcing_set_mono G _ hS'.2
      exact Finset.coe_subset.mpr (Finset.subset_insert _ _)
  · intro S hS T hT heq
    have hS' := Finset.mem_filter.mp hS
    have hT' := Finset.mem_filter.mp hT
    have hScard := Finset.mem_powersetCard_univ.mp hS'.1
    have hTcard := Finset.mem_powersetCard_univ.mp hT'.1
    have hSc : Sum.inl () ∉ S := star_no_center n S (by omega) hS'.2
    have hTc : Sum.inl () ∉ T := star_no_center n T (by omega) hT'.2
    have h := congrArg (fun R : Finset (Unit ⊕ Fin n) => R.erase (Sum.inl ())) heq
    simpa [Finset.erase_insert, hSc, hTc] using h

lemma star_coeff_high_zero (n k : ℕ) (hk : n + 1 < k) :
    (zero_forcing_poly (completeBipartiteGraph Unit (Fin n))).coeff k = 0 := by
  rw [tree_zero_forcing_poly_lower_half_monotone_coeff_eq_card_filter]
  have he : Finset.powersetCard k (Finset.univ : Finset (Unit ⊕ Fin n)) = ∅ := by
    apply Finset.powersetCard_eq_empty.mpr
    simpa [Nat.add_comm] using hk
  simp [he]

lemma star_coeff_top_le_one (n : ℕ) :
    (zero_forcing_poly (completeBipartiteGraph Unit (Fin n))).coeff (n+1) ≤ 1 := by
  rw [tree_zero_forcing_poly_lower_half_monotone_coeff_eq_card_filter]
  refine le_trans (Finset.card_filter_le _ _) ?_
  simp [Finset.card_powersetCard, Nat.add_comm]

lemma star_coeff_n_pos (n : ℕ) (hn : 0 < n) :
    1 ≤ (zero_forcing_poly (completeBipartiteGraph Unit (Fin n))).coeff n := by
  rw [tree_zero_forcing_poly_lower_half_monotone_coeff_eq_card_filter]
  apply Finset.card_pos.mpr
  let leaf : Unit ⊕ Fin n := Sum.inr ⟨0, hn⟩
  let S : Finset (Unit ⊕ Fin n) := Finset.univ.erase leaf
  refine ⟨S, Finset.mem_filter.mpr ⟨?_, ?_⟩⟩
  · apply Finset.mem_powersetCard_univ.mpr
    simp [S, Finset.card_erase_of_mem (Finset.mem_univ leaf)]
  · intro v
    by_cases hv : v = leaf
    · subst v
      apply ZeroForced.step (Sum.inl ()) leaf
      · apply ZeroForced.init
        simp [S, leaf]
      · simp [leaf, completeBipartiteGraph]
      · intro x hx hne
        apply ZeroForced.init
        simpa [S] using hne
    · apply ZeroForced.init
      simpa [S] using hv

lemma star_coeff_zero (n : ℕ) :
    (zero_forcing_poly (completeBipartiteGraph Unit (Fin n))).coeff 0 = 0 := by
  have none {V : Type} (G : SimpleGraph V) {v : V} (h : ZeroForced G ∅ v) : False := by
    induction h with
    | init v hv => exact hv
    | step u w hu hadj hx ihu ihx => exact ihu
  rw [tree_zero_forcing_poly_lower_half_monotone_coeff_eq_card_filter]
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro S hS
  have hs := Finset.mem_filter.mp hS
  have hc := Finset.mem_powersetCard_univ.mp hs.1
  have he : S = ∅ := Finset.card_eq_zero.mp hc
  subst S
  apply none (completeBipartiteGraph Unit (Fin n))
  simpa using hs.2 (Sum.inl ())

/-- The zero forcing polynomial of any star graph K_{1, n} is unimodal. -/
theorem star_graph_zero_forcing_poly_unimodal (n : ℕ) :
    polynomial_is_unimodal (zero_forcing_poly (completeBipartiteGraph Unit (Fin n))) := by
  by_cases hn : n = 0
  · subst n
    refine ⟨1, ?_, ?_⟩
    · intro i j hij hj
      by_cases hi : i = 0
      · subst i
        rw [star_coeff_zero]
        exact Nat.zero_le _
      · have : i = j := by omega
        subst j
        exact le_rfl
    · intro i j hi hij
      by_cases hj : j = 1
      · have hi1 : i = 1 := by omega
        subst i
        subst j
        exact le_rfl
      · rw [star_coeff_high_zero 0 j (by omega)]
        exact Nat.zero_le _
  · have hn' : 1 ≤ n := by omega
    refine ⟨n, ?_, ?_⟩
    · intro i j hij hj
      by_cases hi : i + 2 ≤ n
      · rw [star_coeff_low_zero n i hi]
        exact Nat.zero_le _
      · by_cases h : i = j
        · subst j
          exact le_rfl
        · have hi' : i = n - 1 := by omega
          have hj' : j = n := by omega
          rw [hi', hj']
          exact star_coeff_penult_le n hn'
    · intro i j hi hij
      by_cases hj : n + 1 < j
      · rw [star_coeff_high_zero n j hj]
        exact Nat.zero_le _
      · by_cases h : i = j
        · subst j
          exact le_rfl
        · have hi' : i = n := by omega
          have hj' : j = n + 1 := by omega
          rw [hi', hj']
          exact le_trans (star_coeff_top_le_one n) (star_coeff_n_pos n hn')
