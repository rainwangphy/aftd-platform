import AFTD.Prelude
import AFTD.Kb.Tcs.Op1370TwoRankUpperRelations
import AFTD.Kb.Tcs.Op1370TwoRankLowerRelations

/-!
# op1370_two_rank_response_shapes

Topic: combinatorics   Node: 19e225d8a0b6

Provenance: helper lemma.

For adjacent set ranks, the two rank-one response vectors have the graph-neighbor forms.
-/

open Finset Matrix Polynomial
open scoped BigOperators

theorem op1370_two_rank_response_shapes
    {α V : Type*} [DecidableEq α] [DecidableEq V] (k : ℕ) (A : V → Finset α)
    (hA : Function.Injective A) (levels : ∀ a, (A a).card = k ∨ (A a).card = k + 1)
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hAdj : ∀ a b, G.Adj a b ↔ a ≠ b ∧ (A a ⊆ A b ∨ A b ⊆ A a)) :
    (∀ x a, (if A a ⊆ A x then (-1 : ℚ) ^ ((A x) \ (A a)).card else 0) =
      if (A x).card = k + 1 then
        (if a = x then 1 else if G.Adj x a then -1 else 0)
        else if a = x then 1 else 0) ∧
    (∀ x a, (if A x ⊆ A a then (1 : ℚ) else 0) =
      if (A x).card = k + 1 then
        (if a = x then 1 else 0)
        else if a = x then 1 else if G.Adj x a then 1 else 0) := by
  classical
  constructor
  · intro x a
    by_cases hu : (A x).card = k + 1
    · obtain ⟨hdown, hup, hdiff⟩ :=
        op1370_two_rank_upper_relations k A hA levels G hAdj x hu
      by_cases hax : a = x
      · subst a
        simp [hu]
      · by_cases hg : G.Adj x a
        · have hs : A a ⊆ A x := (hdown a).mpr (Or.inr hg)
          simp [hu, hax, hg, hs, hdiff a hg]
        · have hs : ¬ A a ⊆ A x := by
            intro hs
            exact (hdown a).mp hs |>.elim hax hg
          simp [hu, hax, hg, hs]
    · have hl : (A x).card = k := (levels x).resolve_right hu
      obtain ⟨hdown, hup, hdiff⟩ :=
        op1370_two_rank_lower_relations k A hA levels G hAdj x hl
      by_cases hax : a = x
      · subst a
        simp [hu]
      · have hs : ¬ A a ⊆ A x := fun hs => hax ((hdown a).mp hs)
        simp [hu, hax, hs]
  · intro x a
    by_cases hu : (A x).card = k + 1
    · obtain ⟨hdown, hup, hdiff⟩ :=
        op1370_two_rank_upper_relations k A hA levels G hAdj x hu
      by_cases hax : a = x
      · subst a
        simp [hu]
      · have hs : ¬ A x ⊆ A a := fun hs => hax ((hup a).mp hs)
        simp [hu, hax, hs]
    · have hl : (A x).card = k := (levels x).resolve_right hu
      obtain ⟨hdown, hup, hdiff⟩ :=
        op1370_two_rank_lower_relations k A hA levels G hAdj x hl
      by_cases hax : a = x
      · subst a
        simp [hu]
      · by_cases hg : G.Adj x a
        · have hs : A x ⊆ A a := (hup a).mpr (Or.inr hg)
          simp [hu, hax, hg, hs]
        · have hs : ¬ A x ⊆ A a := by
            intro hs
            exact (hup a).mp hs |>.elim hax hg
          simp [hu, hax, hg, hs]
