import AFTD.Prelude

/-!
# golden_bpe_bias

Topic: algorithms   Node: 29089e6529e6

Provenance: original. Related work: knowledgebase

The golden critical bias p_* is defined as (3 - √5) / 2.
-/

/-- The golden bias p_* = (3 - √5) / 2 where nonoverlapping 00 and mixed 01 merges have equal asymptotic rates. -/
noncomputable def golden_bpe_bias : ℝ := (3 - Real.sqrt 5) / 2
