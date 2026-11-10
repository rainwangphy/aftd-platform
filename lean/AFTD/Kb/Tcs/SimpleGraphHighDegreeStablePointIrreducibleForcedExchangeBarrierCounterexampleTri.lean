import AFTD.Prelude

/-!
# simple_graph_high_degree_stable_point_irreducible_forced_exchange_barrier_counterexample_tri

Topic: graphs   Node: dfe3aad3faae

Provenance: helper lemma. step towards simple_graph_high_degree_stable_point_irreducible_forced_exchange_barrier_counterexample

The three-edge set of the triangle on vertices a, b, c, written as an explicit Finset literal.
-/

/-- The three edges spanned by three vertices, as an explicit finset literal. -/
def simple_graph_high_degree_stable_point_irreducible_forced_exchange_barrier_counterexample_tri (a b c : Fin 12) : Finset (Sym2 (Fin 12)) := {Sym2.mk a b, Sym2.mk b c, Sym2.mk a c}
