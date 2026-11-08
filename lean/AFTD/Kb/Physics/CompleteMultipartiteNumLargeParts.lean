import AFTD.Prelude

/-!
# complete_multipartite_num_large_parts

Topic: quantum_mechanics   Node: a0fc4420e676

Provenance: original. Related work: arXiv:2511.19585

For any finite family of finite types V indexed by ι, complete_multipartite_num_large_parts V is the number of indices i : ι such that Fintype.card (V i) ≥ 4.
-/

/-- Number of parts in a complete multipartite graph family that contain at least four vertices. -/
def complete_multipartite_num_large_parts {ι : Type*} [Fintype ι] [DecidableEq ι]
    (V : ι → Type*) [∀ i, Fintype (V i)] : ℕ := (Finset.univ.filter (fun i => 4 ≤ Fintype.card (V i))).card
