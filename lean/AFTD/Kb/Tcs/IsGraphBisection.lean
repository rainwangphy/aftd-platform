import AFTD.Prelude

/-!
# is_graph_bisection

Topic: graphs   Node: 120f22321733

Provenance: formalization of a published result. Source: arXiv:2611.22760, Section 1

A vertex subset S in a finite type V is a bisection if the sizes of S and its complement Sᶜ differ by at most one: |card(S) - card(Sᶜ)| ≤ 1.
-/

/-- A subset S of vertices in a finite type V is a bisection if |card(S) - card(Sᶜ)| ≤ 1. -/
def is_graph_bisection {V : Type*} [Fintype V] [DecidableEq V] (S : Finset V) : Prop := |(S.card : ℤ) - (Sᶜ.card : ℤ)| ≤ 1
