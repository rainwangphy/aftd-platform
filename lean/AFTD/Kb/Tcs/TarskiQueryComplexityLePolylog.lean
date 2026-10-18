import AFTD.Prelude
import AFTD.Kb.Tcs.TarskiBoxQueryLeSuccHalving
import AFTD.Kb.Tcs.TarskiBoxQueryLeImpQueryComplexity
import AFTD.Kb.Tcs.TarskiBoxQueryLeSmall
import AFTD.Kb.Tcs.TarskiQueryComplexityLe
import AFTD.Kb.Tcs.TarskiBoxQueryLe
import AFTD.Kb.Tcs.TarskiQueryTreeRun
import AFTD.Kb.Tcs.TarskiQueryTreeCost
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Tcs.TarskiQueryTree
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# tarski_query_complexity_le_polylog

Topic: algorithms   Node: ebd96bf5965c

Provenance: helper lemma. step towards tarski_query_complexity_five_le_log_sq

Multidimensional Tarski search is polylogarithmic: for every fixed k there is a constant C with Tarski(n,k) ≤ C·(log₂ n + 2)^k for all n ≥ 1. In particular Tarski(n,5) = O(log⁵ n).
-/

lemma tarski_query_complexity_le_polylog_mono (n k q q' : ℕ)
    (h : tarski_box_query_le n k q) (hqq' : q ≤ q') : tarski_box_query_le n k q' := by
  intro a b hab
  obtain ⟨t, ht⟩ := h a b hab
  exact ⟨t, fun f hf ha hb => ⟨(ht f hf ha hb).1, (ht f hf ha hb).2.1,
    (ht f hf ha hb).2.2.1, (ht f hf ha hb).2.2.2.trans hqq'⟩⟩

lemma tarski_query_complexity_le_polylog_arith (k C p : ℕ) (hp : 2 ≤ p) :
    3 * (k + 1) * p * (C * p^k + 1) + 2^(k+1) ≤ (3 * (k + 1) * (C + 1) + 1) * p^(k+1) := by
  have h1 : 1 ≤ p^k := Nat.one_le_pow k p (by omega)
  have h2 : 2^(k+1) ≤ p^(k+1) := Nat.pow_le_pow_left hp (k+1)
  have h3 : p^(k+1) = p^k * p := Nat.pow_succ p k
  have h4 : C * p^k + 1 ≤ (C + 1) * p^k := by nlinarith
  have hA : 3 * (k + 1) * p * (C * p^k + 1) ≤ 3 * (k + 1) * p * ((C + 1) * p^k) :=
    Nat.mul_le_mul_left (3 * (k + 1) * p) h4
  have hB : 3 * (k + 1) * p * ((C + 1) * p^k) = (3 * (k + 1) * (C + 1)) * p^(k+1) := by
    rw [h3]; ring
  have hA' : 3 * (k + 1) * p * (C * p^k + 1) ≤ (3 * (k + 1) * (C + 1)) * p^(k+1) := by
    rw [← hB]; exact hA
  have hC := Nat.add_le_add hA' h2
  have hD : (3 * (k + 1) * (C + 1)) * p^(k+1) + p^(k+1) = (3 * (k + 1) * (C + 1) + 1) * p^(k+1) := by ring
  exact hC.trans_eq hD

lemma tarski_query_complexity_le_polylog_box (k : ℕ) :
    ∃ C : ℕ, ∀ n : ℕ, 1 ≤ n →
      tarski_box_query_le n k (C * (Nat.log 2 n + 2)^k) := by
  induction k with
  | zero =>
    refine ⟨1, fun n hn => ?_⟩
    haveI : NeZero n := ⟨by omega⟩
    have h : tarski_box_query_le n 0 1 :=
      tarski_box_query_le_small n 0 1 (fun a b hab => by simp)
    simpa using h
  | succ k ih =>
    obtain ⟨C, hC⟩ := ih
    refine ⟨3 * (k + 1) * (C + 1) + 1, fun n hn => ?_⟩
    haveI : NeZero n := ⟨by omega⟩
    have hb := hC n hn
    have hs := tarski_box_query_le_succ_halving n k (C * (Nat.log 2 n + 2)^k) hb
    refine tarski_query_complexity_le_polylog_mono n (k+1) _ _ hs ?_
    exact tarski_query_complexity_le_polylog_arith k C (Nat.log 2 n + 2) (by omega)

/-- Multidimensional Tarski search is polylogarithmic with exponent k; in particular Tarski(n,5) = O(log⁵ n). -/
theorem tarski_query_complexity_le_polylog (k : ℕ) :
    ∃ C : ℕ, ∀ n : ℕ, 1 ≤ n →
      tarski_query_complexity_le n k (C * (Nat.log 2 n + 2) ^ k) := by
  obtain ⟨C, hC⟩ := tarski_query_complexity_le_polylog_box k
  exact ⟨C, fun n hn => tarski_box_query_le_imp_query_complexity n k
    (C * (Nat.log 2 n + 2)^k) hn (hC n hn)⟩
