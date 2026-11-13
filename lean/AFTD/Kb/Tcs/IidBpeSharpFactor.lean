import AFTD.Prelude

/-!
# iid_bpe_sharp_factor

Topic: algorithms   Node: cc9422f13af4

Provenance: formalization of a published result. Source: scout/2611-08671-greedy-byte-pair-encoding-achieves-at-least-0-361-of-the-op.md

The conjectured sharp uniform i.i.d. greedy Byte-Pair Encoding merge factor c = (2 + √2) / 4.
-/

/-- The conjectured sharp uniform i.i.d. greedy Byte-Pair Encoding merge factor (2 + √2) / 4. -/
noncomputable def iid_bpe_sharp_factor : ℝ := (2 + Real.sqrt 2) / 4
