import AFTD.Prelude

/-!
# is_permutationally_convex

Topic: general_equilibrium   Node: e803e99ef9d7

Provenance: formalization of a published result. Source: arXiv:2611.16207 Section 3.2, equation (8); Granot and Huberman (1982)

A cooperative game v on a finite set of players α is permutationally convex if there exists an ordering of the players e : Fin (|α|) ≃ α such that for all indices 0 ≤ j ≤ k ≤ |α| and all coalitions S disjoint from the prefix of the first k players, v([j] ∪ S) + v([k]) ≤ v([k] ∪ S) + v([j]).
-/

/-- A cooperative game is permutationally convex if there is an ordering whose prefixes satisfy the convexity inequality for all disjoint coalitions. -/
def is_permutationally_convex {α : Type*} [DecidableEq α] [Fintype α]
    (v : Finset α → ℝ) : Prop :=
  ∃ e : Fin (Fintype.card α) ≃ α,
    let pref : Fin (Fintype.card α + 1) → Finset α :=
      fun k => (Finset.univ.filter (fun (i : Fin (Fintype.card α)) => (i : ℕ) < (k : ℕ))).image e
    ∀ (k j : Fin (Fintype.card α + 1)), j ≤ k →
      ∀ S : Finset α, Disjoint S (pref k) →
        v (pref j ∪ S) + v (pref k) ≤ v (pref k ∪ S) + v (pref j)
