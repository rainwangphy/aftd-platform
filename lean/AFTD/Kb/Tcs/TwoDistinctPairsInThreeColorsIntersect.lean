import AFTD.Prelude

/-!
# two_distinct_pairs_in_three_colors_intersect

Topic: combinatorics   Node: 763d4b67d8cc

Provenance: helper lemma. Pigeonhole kernel for strong truncation edge compatibility in OP-874.

Two distinct pairs chosen from a three-element palette share a color.
-/

theorem two_distinct_pairs_in_three_colors_intersect
    {Ω : Type*} [DecidableEq Ω] (P : Finset Ω) (hcard : P.card = 3)
    (a b c d : Ω) (ha : a ∈ P) (hb : b ∈ P) (hc : c ∈ P) (hd : d ∈ P)
    (hab : a ≠ b) (hcd : c ≠ d) : a = c ∨ a = d ∨ b = c ∨ b = d := by
  by_contra h
  push_neg at h
  have hs : ({a,b,c,d} : Finset Ω) ⊆ P := by
    intro t ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with rfl | rfl | rfl | rfl
    · exact ha
    · exact hb
    · exact hc
    · exact hd
  have hfour : ({a,b,c,d} : Finset Ω).card = 4 := by
    simp [hab, h.1, h.2.1, h.2.2.1, h.2.2.2, hcd]
  have hle := Finset.card_le_card hs
  omega
