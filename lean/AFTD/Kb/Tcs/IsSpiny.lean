import AFTD.Prelude

/-!
# IsSpiny

Topic: combinatorics   Node: 696171d5db22

Provenance: formalization of a published result. Source: scout/2611-13495-the-largest-ground-set-for-sunflower-free-systems.md:107

For a type α and a finite collection S of finite subsets of α, IsSpiny S holds if and only if for every set A ∈ S, there exists an element x ∈ A such that for all B ∈ S with B ≠ A, x ∉ B.
-/

/-- A finite family of finite sets is spiny if each member contains an element appearing in no other member. -/
def IsSpiny {α : Type*} (S : Finset (Finset α)) : Prop := ∀ A ∈ S, ∃ x ∈ A, ∀ B ∈ S, B ≠ A → x ∉ B
