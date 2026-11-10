import AFTD.Prelude
import AFTD.Kb.Tcs.BpePartialMerge

/-!
# bpe_partial_step

Topic: algorithms   Node: 13c42914f020

Provenance: helper lemma. Definitions for OP-1288, following arXiv:2611.08671, Section 2.

A partial merge replaces an arbitrary nonoverlapping subset of one pair by a fresh symbol, with an unchanged step allowed.
-/

def bpe_partial_step (s t : List ℕ) : Prop :=
  s = t ∨ ∃ a b z, z ∉ s ∧ bpe_partial_merge a b z s t
