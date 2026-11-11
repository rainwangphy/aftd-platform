import AFTD.Prelude

/-!
# is_steiner_system

Topic: graphs   Node: e6e6d244c5d8

Provenance: formalization of a published result. Source: arXiv:2611.11191, Section 2

Given natural numbers t and r, and a set S : Set (Finset α) of finite subsets (blocks) of a type α, is_steiner_system t r S holds if every block B ∈ S has Finset.card B = r, and for every finset T : Finset α with Finset.card T = t, there exists a unique block B ∈ S such that T ⊆ B.
-/

/-- A family of r-subsets S on alpha is a Steiner system S(t, r) if every t-subset is contained in a unique block. -/
def is_steiner_system {α : Type*} (t r : ℕ) (S : Set (Finset α)) : Prop := (∀ B ∈ S, B.card = r) ∧ ∀ T : Finset α, T.card = t → ∃! B ∈ S, T ⊆ B
