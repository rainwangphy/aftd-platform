import AFTD.Prelude

/-!
# nus_collision_subspace

Topic: combinatorics   Node: 3b0041c78326

Provenance: helper lemma. step towards nus_min_card_ge_near_quadratic

The right kernel of the collision matrix of A ⊆ Z/pZ: the submodule of functions x : A → Z/pZ with x a + x b = x c + x d for every collision a + b = c + d inside A. Its codimension, n − finrank, is the F_p-rank of the collision matrix.
-/

/-- The F_p-valued collision-preserving functions on A, i.e. the right kernel of the collision matrix (paper Section 2). -/
def nus_collision_subspace (p : ℕ) (A : Finset (ZMod p)) : Submodule (ZMod p) (↥A → ZMod p) where
  carrier := {x | ∀ a b c d : ↥A, ((a : ZMod p) + (b : ZMod p) = (c : ZMod p) + (d : ZMod p)) → x a + x b = x c + x d}
  zero_mem' := by intro a b c d _; simp
  add_mem' := by
    intro x y hx hy a b c d h
    have h1 := hx a b c d h
    have h2 := hy a b c d h
    simp only [Pi.add_apply]
    calc x a + y a + (x b + y b) = (x a + x b) + (y a + y b) := by ring
      _ = (x c + x d) + (y c + y d) := by rw [h1, h2]
      _ = x c + y c + (x d + y d) := by ring
  smul_mem' := by
    intro r x hx a b c d h
    have h1 := hx a b c d h
    simp only [Pi.smul_apply]
    calc r • x a + r • x b = r • (x a + x b) := by rw [smul_add]
      _ = r • (x c + x d) := by rw [h1]
      _ = r • x c + r • x d := by rw [smul_add]
