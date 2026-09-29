import AFTD.Prelude

/-!
# exists_notMem_of_sum_card_lt

Topic: combinatorics   Node: 69f9041927f2

First moment method (counting form of the union bound): let S be a finite set and let B be a finite family of finite sets. If the sum of the cardinalities of the members of B is strictly less than the cardinality of S, then there is an element of S that belongs to no member of B.
-/

/-- First moment method: if the total size of a finite family of sets is less than `|S|`, some element of `S` avoids them all. -/
theorem exists_notMem_of_sum_card_lt {α : Type*} [DecidableEq α] (S : Finset α) (B : Finset (Finset α))
    (h : ∑ b ∈ B, b.card < S.card) : ∃ ω ∈ S, ∀ b ∈ B, ω ∉ b := by
  by_contra hcon
  push Not at hcon
  have hsub : S ⊆ B.biUnion id := by
    intro ω hω
    obtain ⟨b, hb, hωb⟩ := hcon ω hω
    exact Finset.mem_biUnion.mpr ⟨b, hb, by simpa using hωb⟩
  have h1 : S.card ≤ (B.biUnion id).card := Finset.card_le_card hsub
  have h2 : (B.biUnion id).card ≤ ∑ b ∈ B, b.card := Finset.card_biUnion_le
  linarith
