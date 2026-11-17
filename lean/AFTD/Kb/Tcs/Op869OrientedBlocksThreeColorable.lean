import AFTD.Prelude
import AFTD.Kb.Tcs.Op869OrientThreeColorBlocks

/-!
# op869_oriented_blocks_three_colorable

Topic: online_algorithms   Node: 48ff4060769d

Provenance: helper lemma. arXiv:2610.41516 Lemma 2.5, offline three-colorability step.

A graph made from bipartite blocks is three-colorable when each block belongs to a vertex of a three-colored owner graph, each used block points to at most one differently colored owner, and every cross-edge leaves the designated side toward the block with that target owner.
-/

/-- The offline three-coloring invariant for the fold-simulation block construction. -/
theorem op869_oriented_blocks_three_colorable {X V B : Type} (G : SimpleGraph X) (φ : V → Fin 3) (owner : B → V)
    (target : B → Option V) (selected : B → Bool) (block : X → B) (side : X → Bool)
    (howner : ∀ b v, target b = some v → φ v ≠ φ (owner b))
    (hinner : ∀ x y, G.Adj x y → block x = block y → side x ≠ side y)
    (hcross : ∀ x y, G.Adj x y → block x ≠ block y →
      (target (block x) = some (owner (block y)) ∧ side x = selected (block x)) ∨
      (target (block y) = some (owner (block x)) ∧ side y = selected (block y))) :
    G.Colorable 3 := by
  classical
  obtain ⟨left, right, hlocal⟩ := op869_orient_three_color_blocks φ owner target selected howner
  let col : X → Fin 3 := fun x => if side x then left (block x) else right (block x)
  have havoid : ∀ x, col x ≠ φ (owner (block x)) := by
    intro x
    cases hx : side x <;> simp [col, hx, (hlocal (block x)).1, (hlocal (block x)).2.1]
  have hselected : ∀ x v, target (block x) = some v → side x = selected (block x) → col x = φ v := by
    intro x v ht hs
    have h := (hlocal (block x)).2.2.2 v ht
    simpa [col, hs] using h
  refine ⟨SimpleGraph.Coloring.mk col ?_⟩
  intro x y hxy
  by_cases hb : block x = block y
  · have hs := hinner x y hxy hb
    cases hx : side x <;> cases hy : side y <;>
      simp_all [col, (hlocal (block y)).2.2.1, Ne.symm (hlocal (block y)).2.2.1]
  · rcases hcross x y hxy hb with ⟨ht, hs⟩ | ⟨ht, hs⟩
    · have he := hselected x (owner (block y)) ht hs
      exact fun h => havoid y (h.symm.trans he)
    · have he := hselected y (owner (block x)) ht hs
      exact fun h => havoid x (h.trans he)
