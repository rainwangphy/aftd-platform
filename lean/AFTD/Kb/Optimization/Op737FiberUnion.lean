import AFTD.Prelude

/-!
# op737_fiber_union

Topic: submodular   Node: 9fb386a440b5

Provenance: helper lemma. step towards op_737_block_capacity_submodular_and_base_polytope

The union of the fibers of proj over the blocks in S: the finset of microstates i whose block proj i lies in S.
-/

/-- The union of the fibers of `proj` over the blocks in `S`. -/
def op737_fiber_union {n m : ℕ} (proj : Fin n → Fin m) (S : Finset (Fin m)) : Finset (Fin n) := Finset.univ.filter (fun i => proj i ∈ S)
