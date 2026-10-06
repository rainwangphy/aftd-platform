import AFTD.Prelude

/-!
# maxcut_pair_sum_comm

Topic: equilibria   Node: d4a8c95231de

Provenance: helper lemma. step towards maxcut_optimal_strong_of_degree_le (arXiv:2610.04948, Corollary 9)

The number of bichromatic adjacent ordered pairs (v, w) with v in S and w in T equals the number with v in T and w in S.
-/

theorem maxcut_pair_sum_comm {V : Type} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
    {k : ℕ} (ρ : V → Fin k) (S T : Finset V) :
    ∑ v ∈ S, ∑ w ∈ T, (if G.Adj v w ∧ ρ w ≠ ρ v then 1 else 0 : ℕ) =
      ∑ v ∈ T, ∑ w ∈ S, (if G.Adj v w ∧ ρ w ≠ ρ v then 1 else 0 : ℕ) := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun w _ => ?_
  have e : (G.Adj w v ∧ ρ v ≠ ρ w) ↔ (G.Adj v w ∧ ρ w ≠ ρ v) :=
    ⟨fun h => ⟨h.1.symm, h.2.symm⟩, fun h => ⟨h.1.symm, h.2.symm⟩⟩
  by_cases h : G.Adj v w ∧ ρ w ≠ ρ v
  · rw [if_pos h, if_pos (e.2 h)]
  · rw [if_neg h, if_neg (mt e.1 h)]
