import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# pyranim_seq

Topic: combinatorial_games   Node: 7ed737bf013e

Provenance: helper lemma. step towards pyranim_card_stable_positions

pyranim_seq n is the finite set of all functions l : Fin n → Fin (n+2) that are weakly increasing and satisfy 1 ≤ l i ≤ i+2 for every i. It is the sequence encoding of the stable positions: l i is the least a with (a, i+1) in the position, and the value i+2 encodes an empty column.
-/

/-- Weakly increasing sequences 1 ≤ l i ≤ i+2, the Catalan-indexed model of stable Pyranim positions. -/
noncomputable def pyranim_seq (n : ℕ) : Finset (Fin n → Fin (n + 2)) := Finset.univ.filter (fun l => Monotone l ∧ ∀ i : Fin n, 1 ≤ (l i : ℕ) ∧ (l i : ℕ) ≤ (i : ℕ) + 2)
