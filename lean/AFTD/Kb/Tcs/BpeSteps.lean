import AFTD.Prelude

/-!
# bpe_steps

Topic: algorithms   Node: d771f8e8c5bd

Provenance: helper lemma. Definitions for OP-1288, following arXiv:2611.08671, Section 2.

Exactly k applications of the specified binary relation connect the input and output strings.
-/

def bpe_steps (R : List ℕ → List ℕ → Prop) : ℕ → List ℕ → List ℕ → Prop
  | 0, s, t => s = t
  | k+1, s, t => ∃ u, R s u ∧ bpe_steps R k u t
