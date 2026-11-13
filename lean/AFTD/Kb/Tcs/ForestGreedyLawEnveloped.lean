import AFTD.Prelude
import AFTD.Kb.Tcs.ForestCarpoolTailEnvelope

/-!
# forest_greedy_law_enveloped

Topic: online_algorithms   Node: 38421872d7d1

Provenance: helper lemma. Helper for OP-1106, forest greedy carpooling; related background arXiv:2611.00388.

A finite uniform integer law has one fixed parity, is symmetric, and its positive tail at each positive integer is bounded by the forest carpool envelope.
-/

noncomputable def forest_greedy_law_enveloped (α : Type) [Fintype α] (X : α → ℤ) : Prop := (∃ p : ℤ, ∀ a, X a % 2 = p) ∧ (∀ z : ℤ, (Finset.univ.filter (fun a => X a = z)).card = (Finset.univ.filter (fun a => X a = -z)).card) ∧ (∀ k : ℕ, 1 ≤ k → (((Finset.univ.filter (fun a => (k : ℤ) ≤ X a)).card : ℝ) / (Fintype.card α : ℝ)) ≤ forest_carpool_tail_envelope k)
