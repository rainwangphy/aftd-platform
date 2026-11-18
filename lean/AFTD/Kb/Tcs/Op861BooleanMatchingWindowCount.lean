import AFTD.Prelude
import AFTD.Kb.Tcs.Op861BooleanWeightIntervalCount
import AFTD.Kb.Tcs.Op861BooleanMatchingSetInjective
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# op861_boolean_matching_window_count

Topic: graphs   Node: df5abcdcfdbc

Provenance: helper lemma. Per-block window estimate for op861_disjoint_boolean_windows_count.

For a finite Boolean coordinate set, a fixed bit pattern, an integer offset, and an integer interval with ordered endpoints, the number of assignments whose offset plus number of matching bits lies in the interval is at most the interval length times the largest binomial coefficient for the number of coordinates.
-/

theorem op861_boolean_matching_window_count (β : Type) [Fintype β] [DecidableEq β]
    (pattern : β → Bool) (lo hi offset : ℤ) (hwindow : lo ≤ hi) :
    ((Finset.univ : Finset (β → Bool)).filter (fun v =>
      lo ≤ offset + (((Finset.univ : Finset β).filter (fun t => v t = pattern t)).card : ℤ) ∧
      offset + (((Finset.univ : Finset β).filter (fun t => v t = pattern t)).card : ℤ) ≤ hi)).card ≤
      (hi - lo + 1).toNat * (Fintype.card β).choose (Fintype.card β / 2) := by
  classical
  set n := Fintype.card β
  let m : (β → Bool) → ℕ := fun v => ((Finset.univ : Finset β).filter (fun t => v t = pattern t)).card
  let W : Finset ℕ := (Finset.range (n + 1)).filter (fun s => lo ≤ offset + (s : ℤ) ∧ offset + (s : ℤ) ≤ hi)
  have hsub : ((Finset.univ : Finset (β → Bool)).filter (fun v =>
      lo ≤ offset + (((Finset.univ : Finset β).filter (fun t => v t = pattern t)).card : ℤ) ∧
      offset + (((Finset.univ : Finset β).filter (fun t => v t = pattern t)).card : ℤ) ≤ hi))
      ⊆ W.biUnion (fun s => (Finset.univ : Finset (β → Bool)).filter (fun v => m v = s)) := by
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and, W, Finset.mem_range]
    refine ⟨m v, ⟨?_, hv⟩, rfl⟩
    have := Finset.card_le_univ ((Finset.univ : Finset β).filter (fun t => v t = pattern t))
    simp only [m]; omega
  have hfib : ∀ s, ((Finset.univ : Finset (β → Bool)).filter (fun v => m v = s)).card ≤ n.choose (n / 2) := by
    intro s
    calc _ ≤ ((Finset.univ : Finset β).powersetCard s).card := by
          apply Finset.card_le_card_of_injOn (fun v => (Finset.univ : Finset β).filter (fun t => v t = pattern t))
          · intro v hv
            simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq] at hv
            simp only [Finset.mem_coe,
              Finset.mem_powersetCard, Finset.subset_univ, true_and]
            exact hv
          · intro v _ w _ hvw
            funext t
            have := congrArg (fun S : Finset β => t ∈ S) hvw
            simp only [Finset.mem_filter, Finset.mem_univ, true_and, eq_iff_iff] at this
            cases hv : v t <;> cases hw : w t <;> cases hp : pattern t <;> simp_all
      _ = n.choose s := by rw [Finset.card_powersetCard, Finset.card_univ]
      _ ≤ n.choose (n / 2) := Nat.choose_le_middle s n
  have hW : W.card ≤ (hi - lo + 1).toNat := by
    have hinj : W.card ≤ (Finset.Icc (lo - offset) (hi - offset)).card := by
      apply Finset.card_le_card_of_injOn (fun s : ℕ => (s : ℤ))
      · intro s hs
        simp only [Finset.coe_filter, W, Finset.mem_range, Set.mem_setOf_eq] at hs
        simp only [Finset.coe_Icc, Set.mem_Icc]
        omega
      · intro a _ b _ h
        simpa using h
    rw [Int.card_Icc] at hinj
    have : hi - offset + 1 - (lo - offset) = hi - lo + 1 := by ring
    rw [this] at hinj
    exact hinj
  calc _ ≤ (W.biUnion (fun s => (Finset.univ : Finset (β → Bool)).filter (fun v => m v = s))).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ s ∈ W, ((Finset.univ : Finset (β → Bool)).filter (fun v => m v = s)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ s ∈ W, n.choose (n / 2) := Finset.sum_le_sum fun s _ => hfib s
    _ = W.card * n.choose (n / 2) := by rw [Finset.sum_const, smul_eq_mul]
    _ ≤ _ := Nat.mul_le_mul_right _ hW
