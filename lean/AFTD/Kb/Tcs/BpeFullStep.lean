import AFTD.Prelude
import AFTD.Kb.Tcs.BpeFullMerge

/-!
# bpe_full_step

Topic: algorithms   Node: cd419bb819b2

Provenance: formalization of a published result. Source: scout/2611-08671-greedy-byte-pair-encoding-achieves-at-least-0-361-of-the-op.md:286

A full Byte-Pair Encoding merge step: either the string remains unchanged, or all nonoverlapping occurrences of some pair are replaced left-to-right with a fresh symbol.
-/

/-- A full Byte-Pair Encoding merge step replaces all nonoverlapping occurrences of some pair with a fresh symbol, or leaves the string unchanged. -/
def bpe_full_step (s t : List ℕ) : Prop := s = t ∨ ∃ a b z, z ∉ s ∧ t = bpe_full_merge a b z s
