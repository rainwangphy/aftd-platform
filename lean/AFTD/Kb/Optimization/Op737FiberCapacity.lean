import AFTD.Prelude
import AFTD.Kb.Optimization.Op737FiberUnion

/-!
# op737_fiber_capacity

Topic: submodular   Node: cca86f677dfa

Provenance: helper lemma. step towards op_737_block_capacity_submodular_and_base_polytope

The block capacity induced by a micro capacity f: the value on a set S of blocks is f applied to the union of the fibers over S.
-/

/-- The block capacity induced by a micro capacity: value on S equals value on the union of the fibers over S. -/
noncomputable def op737_fiber_capacity {n m : ℕ} (proj : Fin n → Fin m) (f : Finset (Fin n) → ℝ) (S : Finset (Fin m)) : ℝ := f (op737_fiber_union proj S)
