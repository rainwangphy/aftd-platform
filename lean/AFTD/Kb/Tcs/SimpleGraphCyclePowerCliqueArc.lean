import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphCyclePower
import AFTD.Kb.Tcs.SimpleGraphCyclePowerAdjIffOfBandwidthLt
import AFTD.Kb.Tcs.ZmodIntCastEqIntCastIffOfAbsSubLt
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# simple_graph_cycle_power_clique_arc

Topic: combinatorics   Node: 1cdc2463e7de

Provenance: helper lemma. Uniform graph-to-class-model bridge for OP-205 / RT-1, arXiv:2610.15635. Generalizes the fixed-bandwidth integer-lifting helpers used for radii four and eight. This is geometric bookkeeping, not a research advance.

For n at least 3k+1, every nonempty clique of the k-th cycle power lies in a forward arc of k+1 vertices whose first vertex belongs to the clique.
-/

open Finset

theorem simple_graph_cycle_power_clique_arc
    (n k : ℕ) [NeZero n] (hn : 3 * k + 1 ≤ n)
    (K : Finset (ZMod n)) (hK : K.Nonempty)
    (hc : ∀ u ∈ K, ∀ v ∈ K, u ≠ v → (simple_graph_cycle_power n k).Adj u v) :
    ∃ p ∈ K, ∀ u ∈ K, ∃ a : ℕ, a ≤ k ∧ u = p + (a : ZMod n) := by
  obtain ⟨m, hm⟩ := hK
  have hkn : k < n := by omega
  have hnZ : 3 * (k : ℤ) + 1 ≤ (n : ℤ) := by exact_mod_cast hn
  let S : Finset ℤ := (Icc (-(k : ℤ)) (k : ℤ)).filter (fun e => m + (e : ZMod n) ∈ K)
  have hmem : ∀ e ∈ S, -(k : ℤ) ≤ e ∧ e ≤ k ∧ m + (e : ZMod n) ∈ K := by
    intro e he
    obtain ⟨he, hu⟩ := mem_filter.mp he
    exact ⟨(mem_Icc.mp he).1, (mem_Icc.mp he).2, hu⟩
  have hsurj : ∀ u ∈ K, ∃ e ∈ S, m + (e : ZMod n) = u := by
    intro u hu
    by_cases hum : u = m
    · subst u
      refine ⟨0, ?_, by simp⟩
      simp only [S, mem_filter, mem_Icc]
      exact ⟨⟨by omega, by omega⟩, by simpa using hm⟩
    · obtain ⟨e, _, he, heq⟩ :=
        (simple_graph_cycle_power_adj_iff_of_bandwidth_lt n k hkn m u).mp
          (hc m hm u hu (Ne.symm hum))
      refine ⟨e, ?_, heq.symm⟩
      simp only [S, mem_filter, mem_Icc]
      exact ⟨abs_le.mp he, by simpa only [← heq] using hu⟩
  have hinj : ∀ a ∈ S, ∀ b ∈ S,
      m + (a : ZMod n) = m + (b : ZMod n) → a = b := by
    intro a ha b hb heq
    have ha' := hmem a ha
    have hb' := hmem b hb
    have hab : |a - b| < (n : ℤ) := by
      rcases abs_cases (a - b) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    exact (zmod_intCast_eq_intCast_iff_of_abs_sub_lt n a b hab).mp (add_left_cancel heq)
  have hdiam : ∀ a ∈ S, ∀ b ∈ S, |a - b| ≤ (k : ℤ) := by
    intro a ha b hb
    have ha' := hmem a ha
    have hb' := hmem b hb
    by_cases hab : a = b
    · subst b
      simp
    have hne : m + (a : ZMod n) ≠ m + (b : ZMod n) := fun h => hab (hinj a ha b hb h)
    obtain ⟨e, _, he, heq⟩ :=
      (simple_graph_cycle_power_adj_iff_of_bandwidth_lt n k hkn _ _).mp
        (hc _ ha'.2.2 _ hb'.2.2 hne)
    have he' := abs_le.mp he
    have heqmod : ((b - a : ℤ) : ZMod n) = (e : ZMod n) := by
      push_cast
      calc (b : ZMod n) - a = (m + b) - (m + a) := by ring
           _ = e := by rw [heq]; ring
    have hsmall : |(b - a) - e| < (n : ℤ) := by
      rcases abs_cases ((b - a) - e) with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> omega
    have hei := (zmod_intCast_eq_intCast_iff_of_abs_sub_lt n (b - a) e hsmall).mp heqmod
    rw [← hei] at he
    simpa only [abs_sub_comm] using he
  obtain ⟨z, hz, _⟩ := hsurj m hm
  have hS : S.Nonempty := ⟨z, hz⟩
  let lo := S.min' hS
  have hlo : lo ∈ S := min'_mem S hS
  refine ⟨m + (lo : ZMod n), (hmem lo hlo).2.2, ?_⟩
  intro u hu
  obtain ⟨e, he, heq⟩ := hsurj u hu
  have hle : lo ≤ e := min'_le S e he
  have hbound : e - lo ≤ (k : ℤ) := by
    have hh := hdiam e he lo hlo
    rw [abs_of_nonneg (by omega)] at hh
    exact hh
  refine ⟨(e - lo).toNat, ?_, ?_⟩
  · omega
  · have ht : (((e - lo).toNat : ℕ) : ℤ) = e - lo := Int.toNat_of_nonneg (by omega)
    rw [← heq, ← Int.cast_natCast, ht]
    push_cast
    ring
