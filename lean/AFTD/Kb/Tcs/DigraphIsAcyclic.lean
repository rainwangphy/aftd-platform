import AFTD.Prelude

/-!
# digraph_is_acyclic

Topic: graphs   Node: 541bca0cae95

Provenance: formalization of a published result. Source: arXiv:2610.13798 (On the failure of additivity of inversion numbers for dijoins), Sec. 1 (acyclic digraph: no directed cycle).

A digraph is acyclic when it has no directed cycle: no vertex reaches itself by a nonempty directed walk. For a tournament this means it is transitive.
-/

/-- A digraph is acyclic when it has no directed cycle: no vertex reaches itself by a
nonempty directed walk. -/
def digraph_is_acyclic {V : Type*} (D : Digraph V) : Prop :=
  ∀ x, ¬ Relation.TransGen D.Adj x x
