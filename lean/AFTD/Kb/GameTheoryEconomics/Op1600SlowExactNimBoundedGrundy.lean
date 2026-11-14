import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SlowExactNimGrundy
import AFTD.Kb.GameTheoryEconomics.SlowExactNimStep
import AFTD.Kb.GameTheoryEconomics.SlowExactNimGrundyComp
import AFTD.Kb.GameTheoryEconomics.FinsetMex
import AFTD.Kb.GameTheoryEconomics.SlowExactNimFollowers

/-!
# op_1600_slow_exact_nim_bounded_grundy

Topic: combinatorial_games   Node: 2f56bd331aa2

Provenance: formalization of a published result. Source: arXiv:2611.14546 after Corollary 1

In the normal-play game of slow exact k-Nim on k+2 piles, for every integer k ≥ 3, the range of the Sprague-Grundy function is bounded: there exists an integer C such that every position x : Fin (k + 2) → ℕ satisfies slow_exact_nim_grundy k (k + 2) x ≤ C.
-/

/-- The mex of a finite set of naturals is at most its cardinality. -/
lemma op_1600_slow_exact_nim_bounded_grundy_mex_le_card (s : Finset ℕ) : finset_mex s ≤ s.card := by
  unfold finset_mex
  cases h : List.find? (fun x => decide (x ∉ s)) (List.range (s.card + 1)) with
  | none => simp
  | some y =>
    have hy : y ∈ List.range (s.card + 1) := List.mem_of_find?_eq_some h
    rw [List.mem_range] at hy
    simp only [Option.getD_some]
    omega

/-- From any position on `n` piles there are at most `2 ^ n` distinct followers. -/
lemma op_1600_slow_exact_nim_bounded_grundy_followers_card_le (k n : ℕ) (x : Fin n → ℕ) :
    (slow_exact_nim_followers k n x).card ≤ 2 ^ n := by
  unfold slow_exact_nim_followers
  calc (Finset.image (slow_exact_nim_step x)
        {S ∈ Finset.powersetCard k (Finset.univ : Finset (Fin n)) | ∀ i ∈ S, 0 < x i}).card
      ≤ ({S ∈ Finset.powersetCard k (Finset.univ : Finset (Fin n)) | ∀ i ∈ S, 0 < x i}).card :=
        Finset.card_image_le
    _ ≤ (Finset.powersetCard k (Finset.univ : Finset (Fin n))).card :=
        Finset.card_le_card (Finset.filter_subset _ _)
    _ = (Finset.univ : Finset (Fin n)).card.choose k := Finset.card_powersetCard k _
    _ = n.choose k := by rw [Finset.card_univ, Fintype.card_fin]
    _ ≤ 2 ^ n := Nat.choose_le_two_pow n k

/-- The fuel-bounded Grundy value at any position on `n` piles is at most `2 ^ n`: it is a mex
over the (at most `2 ^ n`) follower values. -/
lemma op_1600_slow_exact_nim_bounded_grundy_comp_le (k n : ℕ) (s : ℕ) (x : Fin n → ℕ) :
    slow_exact_nim_grundy_comp k n s x ≤ 2 ^ n := by
  cases s with
  | zero => rw [show slow_exact_nim_grundy_comp k n 0 x = 0 from rfl]; exact Nat.zero_le _
  | succ t =>
    rw [show slow_exact_nim_grundy_comp k n (t + 1) x
        = finset_mex (Finset.image (fun y => slow_exact_nim_grundy_comp k n t y)
            (slow_exact_nim_followers k n x)) from rfl]
    calc finset_mex (Finset.image (fun y => slow_exact_nim_grundy_comp k n t y)
          (slow_exact_nim_followers k n x))
        ≤ (Finset.image (fun y => slow_exact_nim_grundy_comp k n t y)
          (slow_exact_nim_followers k n x)).card :=
          op_1600_slow_exact_nim_bounded_grundy_mex_le_card _
      _ ≤ (slow_exact_nim_followers k n x).card := Finset.card_image_le
      _ ≤ 2 ^ n := op_1600_slow_exact_nim_bounded_grundy_followers_card_le k n x

/-- OP-1600: Boundedness of Sprague-Grundy values for slow exact k-Nim with k+2 piles. -/
theorem op_1600_slow_exact_nim_bounded_grundy (k : ℕ) (hk : 3 ≤ k) :
    ∃ C : ℕ, ∀ x : Fin (k + 2) → ℕ, slow_exact_nim_grundy k (k + 2) x ≤ C := by
  refine ⟨2 ^ (k + 2), fun x => ?_⟩
  exact op_1600_slow_exact_nim_bounded_grundy_comp_le k (k + 2) (∑ i, x i) x
