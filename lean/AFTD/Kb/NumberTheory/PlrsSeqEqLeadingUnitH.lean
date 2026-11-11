import AFTD.Prelude
import AFTD.Kb.NumberTheory.PlrsSeq
import AFTD.Kb.NumberTheory.LeadingUnitH

/-!
# plrs_seq_eq_leading_unit_h

Topic: elementary_number_theory   Node: a05cac7c46e0

Provenance: helper lemma. arXiv:2611.10200, Section 1

For all natural numbers g, k, N with 1 ≤ g, 1 ≤ k, and 1 ≤ N, the sequence plrs_seq on List.replicate g 1 ++ List.replicate k 0 ++ [N] equals leading_unit_h g k N.
-/

open Finset

def plrs_seq_eq_leading_unit_h_c (g k N : ℕ) : List ℕ :=
  List.replicate g 1 ++ List.replicate k 0 ++ [N]

lemma plrs_seq_eq_leading_unit_h_length (g k N : ℕ) :
    (plrs_seq_eq_leading_unit_h_c g k N).length = g + k + 1 := by
  simp [plrs_seq_eq_leading_unit_h_c, Nat.add_assoc]

lemma plrs_seq_eq_leading_unit_h_getD_lt_g (g k N i : ℕ) (hi : i < g) :
    (plrs_seq_eq_leading_unit_h_c g k N).getD i 0 = 1 := by
  dsimp [plrs_seq_eq_leading_unit_h_c]
  have hlen1 : i < (List.replicate g 1 ++ List.replicate k 0).length := by simp; omega
  rw [List.getD_append _ _ _ _ hlen1]
  have hlen2 : i < (List.replicate g 1).length := by simp; omega
  rw [List.getD_append _ _ _ _ hlen2]
  exact List.getD_replicate 1 hi

lemma plrs_seq_eq_leading_unit_h_getD_middle (g k N i : ℕ) (h1 : g ≤ i) (h2 : i < g + k) :
    (plrs_seq_eq_leading_unit_h_c g k N).getD i 0 = 0 := by
  dsimp [plrs_seq_eq_leading_unit_h_c]
  have hlen1 : i < (List.replicate g 1 ++ List.replicate k 0).length := by simp; omega
  rw [List.getD_append _ _ _ _ hlen1]
  have hlen2 : (List.replicate g 1).length ≤ i := by simp; omega
  rw [List.getD_append_right _ _ _ _ hlen2]
  have hlen3 : (List.replicate g 1).length = g := by simp
  rw [hlen3]
  have hi' : i - g < k := by omega
  exact List.getD_replicate 0 hi'

lemma plrs_seq_eq_leading_unit_h_getD_N (g k N : ℕ) :
    (plrs_seq_eq_leading_unit_h_c g k N).getD (g + k) 0 = N := by
  dsimp [plrs_seq_eq_leading_unit_h_c]
  have hlen : (List.replicate g 1 ++ List.replicate k 0).length ≤ g + k := by simp
  rw [List.getD_append_right _ _ _ _ hlen]
  have : g + k - (List.replicate g 1 ++ List.replicate k 0).length = 0 := by simp
  rw [this]
  rfl

lemma plrs_seq_eq_leading_unit_h_branch1 (g k N n : ℕ) (hn : n + 2 ≤ g + k + 1)
    (ih : ∀ m < n + 2, plrs_seq (plrs_seq_eq_leading_unit_h_c g k N) m = leading_unit_h g k N m) :
    (∑ i ∈ range (n + 1), ((plrs_seq_eq_leading_unit_h_c g k N).getD i 0 : ℤ) * plrs_seq (plrs_seq_eq_leading_unit_h_c g k N) (n + 1 - i)) =
      ∑ j ∈ range (min g (n + 1)), leading_unit_h g k N (n + 2 - (j + 1)) := by
  have h_eq : ∀ i < min g (n + 1),
      ((plrs_seq_eq_leading_unit_h_c g k N).getD i 0 : ℤ) * plrs_seq (plrs_seq_eq_leading_unit_h_c g k N) (n + 1 - i) =
        leading_unit_h g k N (n + 2 - (i + 1)) := by
    intro i hi
    have hig : i < g := by omega
    have hin : n + 1 - i < n + 2 := by omega
    rw [plrs_seq_eq_leading_unit_h_getD_lt_g g k N i hig, ih (n + 1 - i) hin]
    have : n + 2 - (i + 1) = n + 1 - i := by omega
    rw [this, Nat.cast_one, one_mul]
  by_cases hle : n + 1 ≤ g
  · have hmin : min g (n + 1) = n + 1 := min_eq_right hle
    rw [hmin]
    apply sum_congr rfl
    intro i hi
    rw [mem_range] at hi
    have : i < min g (n + 1) := by omega
    exact h_eq i this
  · have hmin : min g (n + 1) = g := min_eq_left (by omega)
    rw [hmin]
    have h_split : range (n + 1) = range (g + (n + 1 - g)) := by
      congr 1; omega
    rw [h_split, sum_range_add]
    have h_zero : ∑ x ∈ range (n + 1 - g),
        ((plrs_seq_eq_leading_unit_h_c g k N).getD (g + x) 0 : ℤ) * plrs_seq (plrs_seq_eq_leading_unit_h_c g k N) (n + 1 - (g + x)) = 0 := by
      apply sum_eq_zero
      intro x hx
      rw [mem_range] at hx
      have h1 : g ≤ g + x := by omega
      have h2 : g + x < g + k := by omega
      rw [plrs_seq_eq_leading_unit_h_getD_middle g k N (g + x) h1 h2, Nat.cast_zero, zero_mul]
    rw [h_zero, add_zero]
    apply sum_congr rfl
    intro i hi
    rw [mem_range] at hi
    have : i < min g (n + 1) := by omega
    exact h_eq i this

lemma plrs_seq_eq_leading_unit_h_branch2 (g k N n : ℕ) (hn : g + k + 1 < n + 2)
    (ih : ∀ m < n + 2, plrs_seq (plrs_seq_eq_leading_unit_h_c g k N) m = leading_unit_h g k N m) :
    (∑ i ∈ range (g + k + 1), ((plrs_seq_eq_leading_unit_h_c g k N).getD i 0 : ℤ) * plrs_seq (plrs_seq_eq_leading_unit_h_c g k N) (n + 1 - i)) =
      (∑ j ∈ range g, leading_unit_h g k N (n + 2 - (j + 1))) + (N : ℤ) * leading_unit_h g k N (n + 2 - (g + k + 1)) := by
  rw [sum_range_add]
  rw [sum_range_add]
  have h_mid : ∑ x ∈ range k,
      ((plrs_seq_eq_leading_unit_h_c g k N).getD (g + x) 0 : ℤ) * plrs_seq (plrs_seq_eq_leading_unit_h_c g k N) (n + 1 - (g + x)) = 0 := by
    apply sum_eq_zero
    intro x hx
    rw [mem_range] at hx
    have h1 : g ≤ g + x := by omega
    have h2 : g + x < g + k := by omega
    rw [plrs_seq_eq_leading_unit_h_getD_middle g k N (g + x) h1 h2, Nat.cast_zero, zero_mul]
  have h_g : ∑ x ∈ range g,
      ((plrs_seq_eq_leading_unit_h_c g k N).getD x 0 : ℤ) * plrs_seq (plrs_seq_eq_leading_unit_h_c g k N) (n + 1 - x) =
        ∑ j ∈ range g, leading_unit_h g k N (n + 2 - (j + 1)) := by
    apply sum_congr rfl
    intro i hi
    rw [mem_range] at hi
    have hin : n + 1 - i < n + 2 := by omega
    rw [plrs_seq_eq_leading_unit_h_getD_lt_g g k N i hi, ih (n + 1 - i) hin]
    have : n + 2 - (i + 1) = n + 1 - i := by omega
    rw [this, Nat.cast_one, one_mul]
  have h_end : ∑ x ∈ range 1,
      ((plrs_seq_eq_leading_unit_h_c g k N).getD (g + k + x) 0 : ℤ) * plrs_seq (plrs_seq_eq_leading_unit_h_c g k N) (n + 1 - (g + k + x)) =
        (N : ℤ) * leading_unit_h g k N (n + 2 - (g + k + 1)) := by
    rw [sum_range_one, add_zero]
    have hin : n + 1 - (g + k) < n + 2 := by omega
    rw [plrs_seq_eq_leading_unit_h_getD_N g k N, ih (n + 1 - (g + k)) hin]
    have : n + 2 - (g + k + 1) = n + 1 - (g + k) := by omega
    rw [this]
  rw [h_mid, add_zero, h_g, h_end]

/-- Agreement between the general PLRS sequence plrs_seq and the specialized leading-unit sequence leading_unit_h on [1^g, 0^k, N]. -/
theorem plrs_seq_eq_leading_unit_h (g k N : ℕ) (hg : 1 ≤ g) (hk : 1 ≤ k) (hN : 1 ≤ N) :
    plrs_seq (List.replicate g 1 ++ List.replicate k 0 ++ [N]) = leading_unit_h g k N := by
  ext m
  change plrs_seq (plrs_seq_eq_leading_unit_h_c g k N) m = leading_unit_h g k N m
  induction' m using Nat.strong_induction_on with m ih
  rcases m with _ | _ | n
  · rw [plrs_seq.eq_1, leading_unit_h.eq_1]
  · rw [plrs_seq.eq_2, leading_unit_h.eq_2]
  · rw [plrs_seq.eq_3, plrs_seq_eq_leading_unit_h_length, leading_unit_h.eq_3]
    split_ifs with hle
    · rw [plrs_seq_eq_leading_unit_h_branch1 g k N n hle ih]
    · have hlt : g + k + 1 < n + 2 := by omega
      rw [plrs_seq_eq_leading_unit_h_branch2 g k N n hlt ih]
