import AFTD.Prelude
import AFTD.Kb.Tcs.HammingBall
import AFTD.Kb.Tcs.HammingRing
import AFTD.Kb.Tcs.IsJointErrorCorrectingDetecting
import AFTD.Kb.Tcs.DisjointHammingBallHammingRingSame
import AFTD.Kb.Tcs.CardHammingBall
import AFTD.Kb.Tcs.CardHammingRing

/-!
# joint_hamming_bound

Topic: information   Node: 510767ffca59

Provenance: formalization of a published result. Source: arXiv:2611.18156 Theorem III.6

Let q ≥ 2, n ≥ 1, and let c, c' be non-negative integers with c + c' ≤ n. If C ⊆ (Fin n → Fin q) is a (c, c') joint error-correcting and detecting code, then |C| * ∑ i ∈ Finset.range (c + 1), Nat.choose n i * (q - 1) ^ i + ∑ j ∈ Finset.Icc (c + 1) (c + c'), Nat.choose n j * (q - 1) ^ j ≤ q ^ n.
-/

/-- Hamming-type upper bound for (c, c') joint error-correcting and detecting codes. -/
theorem joint_hamming_bound (n q c c' : ℕ) (hq : 2 ≤ q) (hn : 1 ≤ n) (hc : c + c' ≤ n)
    (C : Finset (Fin n → Fin q)) (hC : is_joint_error_correcting_detecting c c' C) :
    C.card * (∑ i ∈ Finset.range (c + 1), Nat.choose n i * (q - 1) ^ i) +
      ∑ j ∈ Finset.Icc (c + 1) (c + c'), Nat.choose n j * (q - 1) ^ j ≤ q ^ n := by
  rcases C.eq_empty_or_nonempty with rfl | ⟨x₀, hx₀⟩
  · simp only [Finset.card_empty, zero_mul, zero_add]
    let x₀ : Fin n → Fin q := fun _ => ⟨0, by omega⟩
    rw [← card_hamming_ring n q c c' hq hc x₀]
    have hle := Finset.card_le_univ (hamming_ring c c' x₀)
    have huniv : Fintype.card (Fin n → Fin q) = q ^ n := by simp
    omega
  · have hc_le : c ≤ n := by omega
    have h_card_ball : ∀ x ∈ C, (hamming_ball c x).card = ∑ i ∈ Finset.range (c + 1), Nat.choose n i * (q - 1) ^ i :=
      fun x _ => card_hamming_ball n q c hq hc_le x
    have h_pw : (↑C : Set (Fin n → Fin q)).PairwiseDisjoint (hamming_ball c) :=
      fun x₁ hx₁ x₂ hx₂ hne => hC.1 x₁ hx₁ x₂ hx₂ hne
    have h_union_card : (C.biUnion (hamming_ball c)).card =
        C.card * (∑ i ∈ Finset.range (c + 1), Nat.choose n i * (q - 1) ^ i) := by
      rw [Finset.card_biUnion h_pw]
      rw [Finset.sum_congr rfl h_card_ball]
      simp
    have h_disj : Disjoint (C.biUnion (hamming_ball c)) (hamming_ring c c' x₀) := by
      rw [Finset.disjoint_biUnion_left]
      intro x hx
      exact hC.2 x hx x₀ hx₀
    have h_disj_union : ((C.biUnion (hamming_ball c)) ∪ (hamming_ring c c' x₀)).card =
        (C.biUnion (hamming_ball c)).card + (hamming_ring c c' x₀).card :=
      Finset.card_union_of_disjoint h_disj
    have h_ring_card : (hamming_ring c c' x₀).card =
        ∑ j ∈ Finset.Icc (c + 1) (c + c'), Nat.choose n j * (q - 1) ^ j :=
      card_hamming_ring n q c c' hq hc x₀
    have hle := Finset.card_le_univ ((C.biUnion (hamming_ball c)) ∪ (hamming_ring c c' x₀))
    have huniv : Fintype.card (Fin n → Fin q) = q ^ n := by simp
    omega
