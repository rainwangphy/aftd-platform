import AFTD.Prelude
import AFTD.Kb.Tcs.Op258Bounded
import AFTD.Kb.Tcs.Op258CardFiberSum
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# op_258_one_le_tsum_of_bounded

Topic: combinatorics   Node: e414ffa1b99c

Provenance: helper lemma. step towards op_258_triangle_forcing_implies_decay_ramsey

Let n ≥ 2, let a : ℕ+ → ℝ and let c be an a-bounded colouring of the edges of K_n. Then the ENNReal-sum of the a i is at least 1.
-/

/-- Any a-bounded colouring of K_n with n ≥ 2 forces `1 ≤ Σ a`; in particular a profile with `Σ a < 1` admits no a-bounded colouring at all, so its forcing statements are vacuous. This is why the target's hypothesis `1 < Σ a` is the marginal one. -/
theorem op_258_one_le_tsum_of_bounded (n : ℕ) (hn : 2 ≤ n) (a : ℕ+ → ℝ)
    (c : (SimpleGraph.completeGraph (Fin n)).edgeSet → ℕ+)
    (hc : op_258_bounded a n c) :
    1 ≤ ∑' i : ℕ+, ENNReal.ofReal (a i) := by
  have hpos : 0 < (n.choose 2 : ℝ) := by
    have : 0 < n.choose 2 := Nat.choose_pos hn
    exact_mod_cast this
  have hfiber := op_258_card_fiber_sum n c
  have hle : (∑ i ∈ Finset.univ.image c, (((Finset.univ : Finset (SimpleGraph.completeGraph (Fin n)).edgeSet).filter (fun e => c e = i)).card : ℝ))
      ≤ ∑ i ∈ Finset.univ.image c, (a i * (n.choose 2 : ℝ)) := by
    apply Finset.sum_le_sum
    intro i hi
    exact hc i
  rw [hfiber] at hle
  rw [← Finset.sum_mul] at hle
  have h1 : 1 ≤ ∑ i ∈ Finset.univ.image c, a i := by
    have hmul : 1 * (n.choose 2 : ℝ) ≤ (∑ i ∈ Finset.univ.image c, a i) * (n.choose 2 : ℝ) := by
      simpa using hle
    exact (mul_le_mul_iff_of_pos_right hpos).mp hmul
  have hnonneg : ∀ i ∈ Finset.univ.image c, 0 ≤ a i := by
    intro i hi
    rcases Finset.mem_image.mp hi with ⟨e, -, he⟩
    have hmem : e ∈ (Finset.univ : Finset (SimpleGraph.completeGraph (Fin n)).edgeSet).filter (fun e' => c e' = i) := by
      simp [he]
    have hcard : 1 ≤ ((Finset.univ : Finset (SimpleGraph.completeGraph (Fin n)).edgeSet).filter (fun e' => c e' = i)).card :=
      Finset.card_pos.mpr ⟨e, hmem⟩
    have hcard_real : (1 : ℝ) ≤ (((Finset.univ : Finset (SimpleGraph.completeGraph (Fin n)).edgeSet).filter (fun e' => c e' = i)).card : ℝ) := by
      exact_mod_cast hcard
    have hle_i := hc i
    have : 0 < a i * (n.choose 2 : ℝ) := by linarith
    exact nonneg_of_mul_nonneg_left (by linarith) hpos
  have hone_le_ofReal : 1 ≤ ENNReal.ofReal (∑ i ∈ Finset.univ.image c, a i) := by
    rw [← ENNReal.ofReal_one]
    exact ENNReal.ofReal_le_ofReal h1
  have hsum_eq : ENNReal.ofReal (∑ i ∈ Finset.univ.image c, a i) = ∑ i ∈ Finset.univ.image c, ENNReal.ofReal (a i) :=
    ENNReal.ofReal_sum_of_nonneg hnonneg
  rw [hsum_eq] at hone_le_ofReal
  exact hone_le_ofReal.trans (ENNReal.sum_le_tsum (Finset.univ.image c))
