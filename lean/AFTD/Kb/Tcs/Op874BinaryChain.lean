import AFTD.Prelude

/-!
# op874_binary_chain

Topic: graphs   Node: 20bd8afc3939

Provenance: helper lemma. Finite local-phase reduction for OP-874, https://arxiv.org/abs/2610.41950, Section 2.

Composition of two-state compatibility relations along a finite path.
-/

def op874_binary_chain : List (Bool → Bool → Prop) → Bool → Bool → Prop := fun
  | [], a, b => a = b
  | R :: rs, a, b => ∃ c, R a c ∧ op874_binary_chain rs c b
