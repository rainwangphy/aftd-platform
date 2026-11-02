import AFTD.Prelude

/-!
# seed_tree_1

Topic: quantum_mechanics   Node: db9c19033c8a

Provenance: formalization of a published result. Source: knowledgebase: OP-828; arXiv:2511.19585; arXiv:2610.26814

seed_tree_1 is the simple graph on Fin 16 whose edges are (1, 0), (1, 2), (1, 7), (1, 8), (0, 9), (2, 3), (2, 6), (3, 4), (4, 5), (9, 10), (9, 14), (10, 11), (11, 12), (11, 13), and (14, 15).
-/

/-- The 16-vertex seed tree T with edges [(1, 0), (1, 2), (1, 7), (1, 8), (0, 9), (2, 3), (2, 6), (3, 4), (4, 5), (9, 10), (9, 14), (10, 11), (11, 12), (11, 13), (14, 15)]. -/
def seed_tree_1 : SimpleGraph (Fin 16) := SimpleGraph.fromRel (fun u v => (u, v) ∈ [
    (⟨1, by omega⟩, ⟨0, by omega⟩), (⟨1, by omega⟩, ⟨2, by omega⟩), (⟨1, by omega⟩, ⟨7, by omega⟩),
    (⟨1, by omega⟩, ⟨8, by omega⟩), (⟨0, by omega⟩, ⟨9, by omega⟩), (⟨2, by omega⟩, ⟨3, by omega⟩),
    (⟨2, by omega⟩, ⟨6, by omega⟩), (⟨3, by omega⟩, ⟨4, by omega⟩), (⟨4, by omega⟩, ⟨5, by omega⟩),
    (⟨9, by omega⟩, ⟨10, by omega⟩), (⟨9, by omega⟩, ⟨14, by omega⟩), (⟨10, by omega⟩, ⟨11, by omega⟩),
    (⟨11, by omega⟩, ⟨12, by omega⟩), (⟨11, by omega⟩, ⟨13, by omega⟩), (⟨14, by omega⟩, ⟨15, by omega⟩) ])
