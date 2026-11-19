import AFTD.Prelude
import AFTD.Kb.Tcs.PlaneEmbedding

/-!
# plane_embedding_face_perm

Topic: graphs   Node: 698c3f88abda

Provenance: formalization of a published result. Source: scout/2611-23164-determining-compatible-groups-in-gamma-zonal-labelings.md:99

The facial walk permutation of a plane embedding, mapping each dart d to rot(symm(d)).
-/

/-- The facial walk permutation of a plane embedding. -/
def plane_embedding_face_perm {V : Type*} [Fintype V] [DecidableEq V] {G : SimpleGraph V} [DecidableRel G.Adj] (P : PlaneEmbedding G) : Equiv.Perm G.Dart := Equiv.mk (fun d => P.rot d.symm) (fun d => (P.rot.symm d).symm) (by intro; simp) (by intro; simp)
