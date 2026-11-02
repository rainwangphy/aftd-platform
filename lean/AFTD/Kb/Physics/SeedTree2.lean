import AFTD.Prelude

/-!
# seed_tree_2

Topic: quantum_mechanics   Node: 72a672c632ac

Provenance: formalization of a published result. Source: knowledgebase: OP-828; arXiv:2511.19585; arXiv:2610.26814

seed_tree_2 is the simple graph on Fin 16 whose edges are (1, 0), (1, 2), (1, 7), (0, 8), (2, 3), (2, 6), (3, 4), (4, 5), (8, 9), (8, 13), (8, 15), (9, 10), (10, 11), (10, 12), and (13, 14).
-/

/-- The 16-vertex seed tree T' with edges [(1, 0), (1, 2), (1, 7), (0, 8), (2, 3), (2, 6), (3, 4), (4, 5), (8, 9), (8, 13), (8, 15), (9, 10), (10, 11), (10, 12), (13, 14)]. -/
def seed_tree_2 : SimpleGraph (Fin 16) := SimpleGraph.fromRel (fun u v => (u, v) ∈ [
    (⟨1, by omega⟩, ⟨0, by omega⟩), (⟨1, by omega⟩, ⟨2, by omega⟩), (⟨1, by omega⟩, ⟨7, by omega⟩),
    (⟨0, by omega⟩, ⟨8, by omega⟩), (⟨2, by omega⟩, ⟨3, by omega⟩), (⟨2, by omega⟩, ⟨6, by omega⟩),
    (⟨3, by omega⟩, ⟨4, by omega⟩), (⟨4, by omega⟩, ⟨5, by omega⟩), (⟨8, by omega⟩, ⟨9, by omega⟩),
    (⟨8, by omega⟩, ⟨13, by omega⟩), (⟨8, by omega⟩, ⟨15, by omega⟩), (⟨9, by omega⟩, ⟨10, by omega⟩),
    (⟨10, by omega⟩, ⟨11, by omega⟩), (⟨10, by omega⟩, ⟨12, by omega⟩), (⟨13, by omega⟩, ⟨14, by omega⟩) ])
