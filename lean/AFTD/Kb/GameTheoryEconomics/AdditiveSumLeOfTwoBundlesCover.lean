import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# additive_sum_le_of_two_bundles_cover

Topic: fair_division   Node: e68f81321938

Provenance: helper lemma. for RT-3 (round_robin_pne_envy_zero_ef1_of_two_mul_add_one): at a Round-Robin equilibrium the bundles D1, D2 of two deviations are worth at most v(A_i)

Two-deviation certificate: if two bundles D1, D2, each worth at most v(A) to an agent with nonnegative additive values, together cover (with multiplicity) A plus two distinct goods x, y outside A, then v(x) + v(y) <= v(A).
-/

theorem additive_sum_le_of_two_bundles_cover {G : Type*} [DecidableEq G] (w : G → ℝ)
    (hw : ∀ g, 0 ≤ w g) (A D₁ D₂ : Finset G) (x y : G) (hxy : x ≠ y) (hxA : x ∉ A) (hyA : y ∉ A)
    (h₁ : ∑ g ∈ D₁, w g ≤ ∑ g ∈ A, w g) (h₂ : ∑ g ∈ D₂, w g ≤ ∑ g ∈ A, w g)
    (hcov : ∀ g, (if g ∈ A then 1 else 0) + (if g = x then 1 else 0) + (if g = y then 1 else 0) ≤
      (if g ∈ D₁ then 1 else 0) + (if g ∈ D₂ then 1 else 0 : ℕ)) :
    w x + w y ≤ ∑ g ∈ A, w g := by
  have _ := hxy; have _ := hxA; have _ := hyA
  let S : Finset G := D₁ ∪ D₂ ∪ A ∪ {x} ∪ {y}
  have hD₁ : D₁ ⊆ S := by intro g hg; simp only [S, Finset.mem_union, Finset.mem_singleton]; tauto
  have hD₂ : D₂ ⊆ S := by intro g hg; simp only [S, Finset.mem_union, Finset.mem_singleton]; tauto
  have hA : A ⊆ S := by intro g hg; simp only [S, Finset.mem_union, Finset.mem_singleton]; tauto
  have hx : x ∈ S := by simp only [S, Finset.mem_union, Finset.mem_singleton]; tauto
  have hy : y ∈ S := by simp only [S, Finset.mem_union, Finset.mem_singleton]; tauto
  have hsum : ∑ g ∈ S, ((if g ∈ A then w g else 0) + (if g = x then w g else 0) + (if g = y then w g else 0)) ≤
      ∑ g ∈ S, ((if g ∈ D₁ then w g else 0) + (if g ∈ D₂ then w g else 0)) := by
    apply Finset.sum_le_sum
    intro g _
    have h := hcov g
    have hwg := hw g
    split_ifs at * <;> linarith
  simp only [Finset.sum_add_distrib] at hsum
  simp only [Finset.sum_ite_mem, Finset.inter_eq_right.mpr hA,
             Finset.inter_eq_right.mpr hD₁, Finset.inter_eq_right.mpr hD₂] at hsum
  rw [Finset.sum_ite_eq', if_pos hx] at hsum
  rw [Finset.sum_ite_eq', if_pos hy] at hsum
  linarith
