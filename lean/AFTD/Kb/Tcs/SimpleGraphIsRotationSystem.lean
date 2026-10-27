import AFTD.Prelude

/-!
# simple_graph_is_rotation_system

Topic: graphs   Node: 4e0a63b0ffd1

Provenance: formalization of a published result. Source: Combinatorial embeddings / rotation systems (Mohar-Thomassen, Graphs on Surfaces, Sec. 3.2), used to state the plane embedding of OP-541; arXiv:2610.25886 (Extremal arborescences in graph orientations)

A rotation system of G is a permutation σ of the darts (directed edges) of G that fixes the tail of every dart and permutes the darts at each vertex in a single cycle: the cyclic order of the edges around each vertex in a 2-cell embedding.
-/

/-- σ is a rotation system: it keeps each dart's tail and cycles through all darts at each vertex in one cycle. -/
def simple_graph_is_rotation_system {V : Type*} (G : SimpleGraph V) (σ : Equiv.Perm G.Dart) : Prop :=
  (∀ d, (σ d).fst = d.fst) ∧ ∀ d e : G.Dart, d.fst = e.fst → σ.SameCycle d e
