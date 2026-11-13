import AFTD.Prelude
import AFTD.Kb.Tcs.ForestGreedyLawEnveloped
import AFTD.Kb.Tcs.ForestCarpoolTailEnvelope
import AFTD.Kb.Tcs.ForestGreedyEnvelopedTieBiasBound

/-!
# forest_greedy_enveloped_tie_bias_two

Topic: online_algorithms   Node: 3d4d2df37369

Provenance: helper lemma. Helper for OP-1106, forest greedy carpooling; related background arXiv:2611.00388.

An enveloped fixed-parity law and a fair coin permit an increase from discrepancy 2 with probability at most 1/4.
-/

theorem forest_greedy_enveloped_tie_bias_two (β : Type) [Fintype β] [Nonempty β]
    (Y : β → ℤ) (hY : forest_greedy_law_enveloped β Y) :
  (((Finset.univ.filter (fun p : β × Bool =>
    (2 : ℤ) < Y p.1 ∨ ((2 : ℤ) = Y p.1 ∧ p.2 = true))).card : ℝ) /
    (Fintype.card (β × Bool) : ℝ)) ≤ 1 / 4 := by
  have h := forest_greedy_enveloped_tie_bias_bound β Y hY 2 (by omega)
  norm_num [forest_carpool_tail_envelope, Nat.fib] at h
  simpa only [Fintype.card_prod, Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat] using h
