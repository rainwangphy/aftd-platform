import AFTD.Prelude

/-!
# tournament_covers

Topic: graphs   Node: 7fe5b227dd0f

Provenance: formalization of a published result. Source: arXiv:2610.40521 Definition 3

A vertex w covers a vertex v in a tournament T if w -> v and w -> x for every out-neighbor x of v.
-/

/-- A vertex w covers v in a tournament T if w points to v and to every out-neighbor of v. -/
def tournament_covers {V : Type*} (T : Digraph V) (w v : V) : Prop := T.Adj w v ∧ ∀ x, T.Adj v x → T.Adj w x
