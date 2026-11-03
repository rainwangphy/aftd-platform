import AFTD.Prelude
import AFTD.Kb.Tcs.DualMelasJointPatternProb
import AFTD.Kb.Tcs.DualMelasPatternCountLe
import AFTD.Kb.Tcs.DualMelasPatternCount
import AFTD.Kb.Tcs.CyclicRotateLeft

/-!
# dual_melas_joint_pattern_prob_sum

Topic: information   Node: 66f989de3a4d

Provenance: helper lemma. step towards dual_melas_adjacent_cyclic_patterns_bivariate_poisson_limit

For any field F finite-dimensional over ZMod 2, natural number k, and elements α, c ∈ F, the sum of dual_melas_joint_pattern_prob k α c a b over all a, b < 2^k equals 1.
-/

private lemma dual_melas_joint_pattern_prob_sum_aux1 {X : Type*} [DecidableEq X] (s : Finset X)
    (f : X → ℕ) (N : ℕ) (h : ∀ x ∈ s, f x < N) :
    ∑ b ∈ Finset.range N, (s.filter (fun x => f x = b)).card = s.card :=
  (Finset.card_eq_sum_card_fiberwise (f := f) (s := s) (t := Finset.range N)
    (fun x hx => Finset.mem_range.mpr (h x hx))).symm

private lemma dual_melas_joint_pattern_prob_sum_aux2 {X : Type*} [Fintype X] [DecidableEq X]
    (f g : X → ℕ) (N : ℕ) (hf : ∀ x, f x < N) (hg : ∀ x, g x < N) :
    ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N,
      (Finset.univ.filter (fun x => f x = a ∧ g x = b)).card = Fintype.card X := by
  have step : ∀ a, ∑ b ∈ Finset.range N,
      (Finset.univ.filter (fun x => f x = a ∧ g x = b)).card =
      (Finset.univ.filter (fun x => f x = a)).card := by
    intro a
    rw [← dual_melas_joint_pattern_prob_sum_aux1
      (Finset.univ.filter (fun x => f x = a)) g N (fun x _ => hg x)]
    apply Finset.sum_congr rfl
    intro b _
    rw [Finset.filter_filter]
  have h1 : (∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N,
      (Finset.univ.filter (fun x => f x = a ∧ g x = b)).card) =
      ∑ a ∈ Finset.range N, (Finset.univ.filter (fun x => f x = a)).card :=
    Finset.sum_congr rfl (fun a _ => step a)
  rw [h1, ← Finset.card_univ]
  exact dual_melas_joint_pattern_prob_sum_aux1 Finset.univ f N (fun x _ => hf x)

/-- Sum of dual Melas joint pattern probabilities over range 2^k is 1. -/
theorem dual_melas_joint_pattern_prob_sum
    {F : Type*} [Field F] [Algebra (ZMod 2) F] [FiniteDimensional (ZMod 2) F]
    (k : ℕ) (α c : F) :
    ∑ a ∈ Finset.range (2 ^ k), ∑ b ∈ Finset.range (2 ^ k),
      dual_melas_joint_pattern_prob k α c a b = 1 := by
  unfold dual_melas_joint_pattern_prob
  have hbound : ∀ w : Fin k → ZMod 2,
      dual_melas_pattern_count k α c w < 2 ^ k := by
    intro w
    have hp : 0 < 2 ^ k := pow_pos (by norm_num) k
    have h := dual_melas_pattern_count_le k α c w
    omega
  have hcard : ∑ a ∈ Finset.range (2 ^ k), ∑ b ∈ Finset.range (2 ^ k),
      (Finset.univ.filter (fun w : Fin k → ZMod 2 =>
        dual_melas_pattern_count k α c w = a ∧
        dual_melas_pattern_count k α c (cyclic_rotate_left k w) = b)).card
      = (2 : ℕ) ^ k := by
    have h := dual_melas_joint_pattern_prob_sum_aux2
      (fun w : Fin k → ZMod 2 => dual_melas_pattern_count k α c w)
      (fun w : Fin k → ZMod 2 => dual_melas_pattern_count k α c (cyclic_rotate_left k w))
      (2 ^ k) hbound (fun x => hbound (cyclic_rotate_left k x))
    rw [h]
    simp [ZMod.card]
  have hcardR : (∑ a ∈ Finset.range (2 ^ k), ∑ b ∈ Finset.range (2 ^ k),
      ((Finset.univ.filter (fun w : Fin k → ZMod 2 =>
        dual_melas_pattern_count k α c w = a ∧
        dual_melas_pattern_count k α c (cyclic_rotate_left k w) = b)).card : ℝ))
      = (2 : ℝ) ^ k := by
    have h := congrArg (fun n : ℕ => (n : ℝ)) hcard
    push_cast at h ⊢
    exact h
  have hD : (2 : ℝ) ^ k ≠ 0 := ne_of_gt (pow_pos (by norm_num) k)
  calc ∑ a ∈ Finset.range (2 ^ k), ∑ b ∈ Finset.range (2 ^ k),
        ((Finset.univ.filter (fun w : Fin k → ZMod 2 =>
          dual_melas_pattern_count k α c w = a ∧
          dual_melas_pattern_count k α c (cyclic_rotate_left k w) = b)).card : ℝ) /
            (2 : ℝ) ^ k
      = ∑ a ∈ Finset.range (2 ^ k),
          (∑ b ∈ Finset.range (2 ^ k),
            ((Finset.univ.filter (fun w : Fin k → ZMod 2 =>
              dual_melas_pattern_count k α c w = a ∧
              dual_melas_pattern_count k α c (cyclic_rotate_left k w) = b)).card : ℝ)) /
              (2 : ℝ) ^ k :=
        Finset.sum_congr rfl (fun a _ =>
          (Finset.sum_div (Finset.range (2 ^ k)) _ _).symm)
    _ = (∑ a ∈ Finset.range (2 ^ k), ∑ b ∈ Finset.range (2 ^ k),
          ((Finset.univ.filter (fun w : Fin k → ZMod 2 =>
            dual_melas_pattern_count k α c w = a ∧
            dual_melas_pattern_count k α c (cyclic_rotate_left k w) = b)).card : ℝ)) /
            (2 : ℝ) ^ k :=
        (Finset.sum_div (Finset.range (2 ^ k)) _ _).symm
    _ = (2 : ℝ) ^ k / (2 : ℝ) ^ k := by rw [hcardR]
    _ = 1 := div_self hD
