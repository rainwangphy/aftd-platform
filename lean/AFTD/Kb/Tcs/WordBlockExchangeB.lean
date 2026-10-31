import AFTD.Prelude
import AFTD.Kb.Tcs.MaskURuns
import AFTD.Kb.Tcs.IsWordMask
import AFTD.Kb.Tcs.WordBlockExchangeAfter
import AFTD.Kb.Tcs.WordBlockExchange
import AFTD.Kb.Tcs.WordBlockExchangeIsCommuting

/-!
# word_block_exchange_b

Topic: automata   Node: 43829161d685

Provenance: formalization of a published result. Source: arXiv:2610.39941, Section 4, equation (2)

The noncommuting minimum degree word_block_exchange_b E u v is the infimum in WithTop Nat of mask_u_runs N over all noncommuting masks N of the exchanged word word_block_exchange_after E satisfying is_word_mask u v (word_block_exchange_after E) N and ¬ word_block_exchange_is_commuting E N.
-/

/-- Minimum run count over all noncommuting masks of XBAY for exchange E, or top if none exists. -/
noncomputable def word_block_exchange_b {α : Type*} (E : WordBlockExchange α) (u v : List α) : WithTop ℕ :=
  sInf { (mask_u_runs N : WithTop ℕ) | (N : List Bool) (_ : is_word_mask u v (word_block_exchange_after E) N) (_ : ¬ word_block_exchange_is_commuting E N) }
