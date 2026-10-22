import AFTD.Prelude

/-!
# ve_dominates_inside

Topic: graphs   Node: ba6e205875cd

Provenance: helper lemma. step towards not_is_fix_v0_of_neighbors_unreachable

A vertex set S ve-dominates inside a vertex set A if every edge of G with both endpoints in A is ve-dominated by a vertex of S.
-/

/-- `S` ve-dominates every edge whose two endpoints lie in `A`; with `A = univ` this is `is_ve_dominating G S`. -/
def ve_dominates_inside {V : Type*} (G : SimpleGraph V) (S : Set V) (A : Set V) : Prop := ∀ ⦃x y : V⦄, G.Adj x y → x ∈ A → y ∈ A → ∃ u ∈ S, u = x ∨ G.Adj u x ∨ u = y ∨ G.Adj u y
