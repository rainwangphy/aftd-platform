import AFTD.Prelude
import AFTD.Kb.Tcs.ShiftedGeometricDistribution
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# shifted_geometric_distribution_hasSum

Topic: information   Node: 76d110b770ef

Provenance: helper lemma. arXiv:2611.16066, Theorem 5.1

For any parameter 0 ≤ a < 1 and shift L ∈ ℤ, the shifted geometric distribution G_L has sum 1 over ℤ.
-/

/-- The shifted geometric distribution G_L has total probability mass 1 when 0 ≤ a < 1. -/
lemma shifted_geometric_distribution_hasSum {a : ℝ} (ha0 : 0 ≤ a) (ha1 : a < 1) (L : ℤ) :
    HasSum (shifted_geometric_distribution a L) 1 := by
  let f : ℤ → ℝ := shifted_geometric_distribution a L
  let e : ℕ ≃ {s : ℤ // L ≤ s} :=
    { toFun := fun n => ⟨L + n, by omega⟩
      invFun := fun s => (s.1 - L).toNat
      left_inv := by
        intro n
        show ((L + (n : ℤ) - L).toNat : ℕ) = n
        have h : L + (n : ℤ) - L = (n : ℤ) := by omega
        rw [h, Int.toNat_natCast]
      right_inv := by
        intro s
        apply Subtype.ext
        show L + ((s.1 - L).toNat : ℕ) = s.1
        have h : 0 ≤ s.1 - L := sub_nonneg.mpr s.2
        rw [Int.toNat_of_nonneg h]
        omega }
  have hsupp : Function.support f ⊆ Set.Ici L := by
    intro x hx
    by_contra hxL
    have hxL' : ¬ L ≤ x := by simpa using hxL
    exact hx (by simp [f, shifted_geometric_distribution, hxL'])
  have hcomp : (fun n : ℕ => (f ∘ Subtype.val) (e n)) = fun n : ℕ => (1 - a) * a ^ n := by
    funext n
    simp [f, shifted_geometric_distribution, e]
  have hgeom : HasSum (fun n : ℕ => (1 - a) * a ^ n) 1 := by
    have hgeom : HasSum (fun n : ℕ => a ^ n) (1 - a)⁻¹ :=
      hasSum_geometric_of_lt_one ha0 ha1
    have hne : (1 : ℝ) - a ≠ 0 := by linarith
    simpa [hne] using hgeom.mul_left (1 - a)
  have hcomp_sum : HasSum (fun n : ℕ => (f ∘ Subtype.val) (e n)) 1 := by
    rw [hcomp]
    exact hgeom
  have hsub : HasSum (f ∘ Subtype.val) 1 :=
    (Equiv.hasSum_iff e).mp hcomp_sum
  have hmain : HasSum f 1 :=
    (hasSum_subtype_iff_of_support_subset hsupp).mp hsub
  simpa [f] using hmain
