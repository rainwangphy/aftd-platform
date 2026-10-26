import AFTD.Prelude

/-!
# is_cograph

Topic: graphs   Node: 7f1b7b510d8d

Provenance: formalization of a published result. Source: arXiv:2610.13820, Fact 4.4

A graph F is a cograph if it does not contain an induced path on four vertices (P₄).
-/

/-- A graph is a cograph if it contains no induced path of four vertices. -/
def is_cograph {α : Type*} (F : SimpleGraph α) : Prop := ¬ ∃ (a b c d : α),
    a ≠ b ∧ a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d ∧ c ≠ d ∧
    F.Adj a b ∧ F.Adj b c ∧ F.Adj c d ∧
    ¬ F.Adj a c ∧ ¬ F.Adj a d ∧ ¬ F.Adj b d
