import AFTD.Prelude
import AFTD.Kb.Tcs.TernaryAffineHyperplane
import AFTD.Kb.Tcs.TernarySinglePointRepair
import AFTD.Kb.Tcs.TernaryAffineHyperplaneCard

/-!
# ternary_single_point_repair_card

Topic: combinatorics   Node: d5053c2c0998

Provenance: helper lemma. arXiv:2610.32789, Section 3.1

For every explicit integer n ≥ 1, every vector a : Fin n → ZMod 3 with all coordinates nonzero, every scalar b : ZMod 3, every point p in ternary_affine_hyperplane n a b, and every vector ε : Fin n → ZMod 3 with all coordinates nonzero, the finite set ternary_single_point_repair n (ternary_affine_hyperplane n a b) p ε has cardinality 3^(n - 1) + n - 1.
-/

/-- The single-point repair of an affine hyperplane has size 3^(n-1) + n - 1. -/
theorem ternary_single_point_repair_card (n : ℕ) (hn : 1 ≤ n) (a : Fin n → ZMod 3) (ha : ∀ i, a i ≠ 0) (b : ZMod 3) (p : Fin n → ZMod 3) (hp : p ∈ ternary_affine_hyperplane n a b) (ε : Fin n → ZMod 3) (hε : ∀ i, ε i ≠ 0) : (ternary_single_point_repair n (ternary_affine_hyperplane n a b) p ε).card = 3 ^ (n - 1) + n - 1 := by
  open Finset in
  have sum_update (i : Fin n) :
      (∑ j, a j * Function.update p i (p i + ε i) j) = (∑ j, a j * p j) + a i * ε i := by
    have h1 : (∑ j, a j * Function.update p i (p i + ε i) j) =
        a i * Function.update p i (p i + ε i) i + ∑ j ∈ univ.erase i, a j * Function.update p i (p i + ε i) j := by
      rw [← add_sum_erase univ (fun j => a j * Function.update p i (p i + ε i) j) (mem_univ i)]
    have h2 : (∑ j, a j * p j) = a i * p i + ∑ j ∈ univ.erase i, a j * p j := by
      rw [← add_sum_erase univ (fun j => a j * p j) (mem_univ i)]
    have h3 : (∑ j ∈ univ.erase i, a j * Function.update p i (p i + ε i) j) =
        ∑ j ∈ univ.erase i, a j * p j := by
      apply sum_congr rfl
      intro j hj
      have hj' : j ≠ i := mem_erase.mp hj |>.1
      rw [Function.update_of_ne hj']
    rw [h1, h2, h3, Function.update_self]
    ring

  have h_not_mem (i : Fin n) : Function.update p i (p i + ε i) ∉ ternary_affine_hyperplane n a b := by
    intro hmem
    rw [ternary_affine_hyperplane, Finset.mem_filter] at hmem hp
    have hmem' := hmem.2
    have hp' := hp.2
    rw [sum_update i] at hmem'
    rw [hp'] at hmem'
    have hzero : a i * ε i = 0 := by
      apply_fun (· - b) at hmem'
      ring_nf at hmem'
      exact hmem'
    cases mul_eq_zero.mp hzero with
    | inl ha0 => exact ha i ha0
    | inr hε0 => exact hε i hε0

  have hinj : Function.Injective (fun i => Function.update p i (p i + ε i)) := by
    intro i j h
    by_contra hij
    dsimp only at h
    have h1 := congr_fun h i
    rw [Function.update_self] at h1
    rw [Function.update_of_ne hij] at h1
    have : ε i = 0 := by
      apply_fun (· - p i) at h1
      ring_nf at h1
      exact h1
    exact hε i this

  have hdisj : Disjoint ((ternary_affine_hyperplane n a b).erase p)
      (Finset.image (fun i => Function.update p i (p i + ε i)) Finset.univ) := by
    rw [Finset.disjoint_right]
    intro x hx
    rw [Finset.mem_image] at hx
    rcases hx with ⟨i, -, rfl⟩
    intro hx'
    have hx'' : Function.update p i (p i + ε i) ∈ ternary_affine_hyperplane n a b :=
      Finset.mem_of_mem_erase hx'
    exact h_not_mem i hx''

  have hcard_H : (ternary_affine_hyperplane n a b).card = 3 ^ (n - 1) :=
    ternary_affine_hyperplane_card n hn a ha b

  have hcard_erase : ((ternary_affine_hyperplane n a b).erase p).card = 3 ^ (n - 1) - 1 := by
    rw [Finset.card_erase_of_mem hp, hcard_H]

  have hcard_image : (Finset.image (fun i => Function.update p i (p i + ε i)) Finset.univ).card = n := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]

  change ((ternary_affine_hyperplane n a b).erase p ∪
      Finset.image (fun i => Function.update p i (p i + ε i)) Finset.univ).card = 3 ^ (n - 1) + n - 1
  rw [Finset.card_union_of_disjoint hdisj, hcard_erase, hcard_image]
  have : 1 ≤ 3 ^ (n - 1) := Nat.one_le_pow (n - 1) 3 (by decide)
  omega
