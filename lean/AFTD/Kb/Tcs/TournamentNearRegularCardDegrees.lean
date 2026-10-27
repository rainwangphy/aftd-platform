import AFTD.Prelude
import AFTD.Kb.Tcs.TournamentIsNearRegular
import AFTD.Kb.Tcs.DigraphIsTournament
import AFTD.Kb.Tcs.DigraphOutCount
import AFTD.Kb.Tcs.TournamentSumOutCount
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# tournament_near_regular_card_degrees

Topic: graphs   Node: 62c4c11f5c89

Provenance: original. Related work: arXiv:2610.25886

In any near-regular tournament on 2m vertices with m ≥ 1, exactly m vertices have out-degree m - 1 and exactly m vertices have out-degree m.
-/

/-- In a near-regular tournament of order 2m, exactly m vertices have out-degree m - 1 and m vertices have out-degree m. -/
theorem tournament_near_regular_card_degrees (m : ℕ) (hm : 1 ≤ m)
    (T : Digraph (Fin (2 * m))) [DecidableRel T.Adj] (hT : digraph_is_tournament T)
    (hnr : tournament_is_near_regular m T) :
    (Finset.univ.filter (fun v => digraph_out_count T v = m - 1)).card = m ∧
    (Finset.univ.filter (fun v => digraph_out_count T v = m)).card = m := by
  open Finset in
  let A := univ.filter (fun v => digraph_out_count T v = m - 1)
  let B := univ.filter (fun v => digraph_out_count T v = m)
  have hdisj : Disjoint A B := by
    rw [disjoint_filter]
    intro x _ h1 h2
    have : m - 1 ≠ m := by omega
    exact this (h1.symm.trans h2)
  have huniv : A ∪ B = univ := by
    ext v
    simp only [mem_univ, iff_true]
    rw [mem_union, mem_filter, mem_filter]
    simp only [mem_univ, true_and]
    exact hnr v
  have hcard_sum : A.card + B.card = 2 * m := by
    have h1 : (A ∪ B).card = (univ : Finset (Fin (2 * m))).card := congrArg card huniv
    rw [card_union_of_disjoint hdisj, card_fin] at h1
    exact h1
  have hsum_split : (∑ v, digraph_out_count T v) = (∑ v ∈ A, digraph_out_count T v) + (∑ v ∈ B, digraph_out_count T v) := by
    rw [← huniv, sum_union hdisj]
  have hsum_A : (∑ v ∈ A, digraph_out_count T v) = A.card * (m - 1) := by
    have : (∑ v ∈ A, digraph_out_count T v) = ∑ v ∈ A, (m - 1) := by
      apply sum_congr rfl
      intro x hx
      rw [mem_filter] at hx
      exact hx.2
    rw [this, sum_const, Nat.nsmul_eq_mul]
  have hsum_B : (∑ v ∈ B, digraph_out_count T v) = B.card * m := by
    have : (∑ v ∈ B, digraph_out_count T v) = ∑ v ∈ B, m := by
      apply sum_congr rfl
      intro x hx
      rw [mem_filter] at hx
      exact hx.2
    rw [this, sum_const, Nat.nsmul_eq_mul]
  have htot := tournament_sum_out_count (2 * m) T hT
  have hdiv : (2 * m) * (2 * m - 1) / 2 = m * (2 * m - 1) := by
    have : (2 * m) * (2 * m - 1) = 2 * (m * (2 * m - 1)) := by ring
    rw [this, Nat.mul_div_cancel_left _ (by decide)]
  rw [hdiv] at htot
  rw [hsum_split, hsum_A, hsum_B] at htot
  have hm2 : 1 ≤ 2 * m := by omega
  have hA : A.card = m ∧ B.card = m := by
    zify [hm, hm2] at hcard_sum htot ⊢
    constructor <;> nlinarith
  exact hA
