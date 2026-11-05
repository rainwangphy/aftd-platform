import AFTD.Prelude
import AFTD.Kb.Tcs.SatisfiesGeodeticProductCondition
import AFTD.Kb.Tcs.SatisfiesGeodeticCCondition
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# geodetic_c_condition_iff_product_condition_three

Topic: graphs   Node: 65172e89bfd5

Provenance: formalization of a published result. Source: arXiv:2611.05762, Sec. 4.3

Let d ≥ 1 and let c : Fin d → ℕ be a monotone nondecreasing sequence with c(0) = 1. Then c satisfies the geodesic product condition for K = 3 if and only if c satisfies the arithmetic geodetic condition for K = 3 (that is, c(i) = 1 for all i < d - 1 and c(d - 1) ≤ 3).
-/

/-- For nondecreasing c starting with 1, the product condition for K=3 is equivalent to c_i = 1 for i < d-1 and c_{d-1} ≤ 3. -/
theorem geodetic_c_condition_iff_product_condition_three (d : ℕ) (hd : 1 ≤ d)
    (c : Fin d → ℕ) (hc0 : c ⟨0, hd⟩ = 1) (hmono : Monotone c) :
    satisfies_geodetic_product_condition d c 3 ↔ satisfies_geodetic_c_condition d c 3 := by
  constructor
  · intro hprod
    have hc_ge_one : ∀ j : Fin d, 1 ≤ c j := fun j => by
      have hj : (⟨0, hd⟩ : Fin d) ≤ j := Nat.zero_le _
      have h := hmono hj
      rwa [hc0] at h
    refine ⟨?_, ?_⟩
    · intro i hi
      by_contra hne
      have h2 : 2 ≤ c i := by
        have : 1 ≤ c i := hc_ge_one i
        omega
      let next_i : Fin d := ⟨i.val + 1, hi⟩
      have hi_le : i ≤ next_i := Nat.le_succ i.val
      have hnext_ge : 2 ≤ c next_i := h2.trans (hmono hi_le)
      have h_ne : i ≠ next_i := by
        intro h
        have hval : i.val = next_i.val := congrArg Fin.val h
        dsimp [next_i] at hval
        omega
      have hi_mem : i ∈ Finset.Iic next_i := Finset.mem_Iic.mpr hi_le
      have hnext_mem : next_i ∈ Finset.Iic next_i := Finset.mem_Iic.mpr le_rfl
      have hmul : c i * c next_i ≤ ∏ j ∈ Finset.Iic next_i, c j :=
        Finset.mul_le_prod (fun j _ => hc_ge_one j) hi_mem hnext_mem h_ne
      have hprod_le : ∏ j ∈ Finset.Iic next_i, c j ≤ 3 := hprod next_i
      have : 4 ≤ 3 := by
        calc 4 = 2 * 2 := by rfl
        _ ≤ c i * c next_i := Nat.mul_le_mul h2 hnext_ge
        _ ≤ ∏ j ∈ Finset.Iic next_i, c j := hmul
        _ ≤ 3 := hprod_le
      omega
    · intro i _
      have hi_mem : i ∈ Finset.Iic i := Finset.mem_Iic.mpr le_rfl
      have hle : c i ≤ ∏ j ∈ Finset.Iic i, c j :=
        Finset.single_le_prod' (fun j _ => hc_ge_one j) hi_mem
      exact hle.trans (hprod i)
  · intro hc i
    have hi_mem : i ∈ Finset.Iic i := Finset.mem_Iic.mpr le_rfl
    have h_single : ∀ b ∈ Finset.Iic i, b ≠ i → c b = 1 := by
      intro b hb hne
      have hle : b ≤ i := Finset.mem_Iic.mp hb
      have hlt : b < i := lt_of_le_of_ne hle hne
      have hbd : b.val + 1 < d := by
        have : i.val < d := i.isLt
        have : b.val < i.val := hlt
        omega
      exact hc.1 b hbd
    have hprod : ∏ j ∈ Finset.Iic i, c j = c i :=
      Finset.prod_eq_single_of_mem i hi_mem h_single
    rw [hprod]
    have : i.val + 1 ≤ d := i.isLt
    rcases eq_or_lt_of_le this with h_eq | h_lt
    · exact hc.2 i h_eq
    · have := hc.1 i h_lt
      omega
