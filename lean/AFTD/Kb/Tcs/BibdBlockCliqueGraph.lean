import AFTD.Prelude
import AFTD.Kb.Tcs.BIBD

/-!
# bibd_block_clique_graph

Topic: graphs   Node: 8dba96768149

Provenance: formalization of a published result. Source: arXiv:2611.05762 Sec. 6.9

The modified block-clique graph K_v^*(D) of a balanced incomplete block design D with parameters (v, b, r, k, λ) is the simple graph on vertex set X ⊕ (B × Fin k) whose edges connect each local vertex (b, j) to the point vertex D.block_pts b j, and connect distinct local vertices (b, j₁) and (b, j₂) belonging to the same block b.
-/

/-- The modified block-clique graph K_v^*(r, k, λ) of a BIBD D on vertex set X ⊕ (B × Fin k). -/
def bibd_block_clique_graph {X B : Type*} {v b r k lam : ℕ} (D : BIBD X B v b r k lam) :
    SimpleGraph (X ⊕ (B × Fin k)) := {
  Adj := fun u v =>
    match u, v with
    | Sum.inl x, Sum.inr (b_idx, j) => D.block_pts b_idx j = x
    | Sum.inr (b_idx, j), Sum.inl x => D.block_pts b_idx j = x
    | Sum.inr (b1, j1), Sum.inr (b2, j2) => b1 = b2 ∧ j1 ≠ j2
    | Sum.inl _, Sum.inl _ => False
  symm := ⟨by
    intro u v h
    rcases u with x | ⟨b1, j1⟩ <;> rcases v with y | ⟨b2, j2⟩ <;>
      simp_all [ne_comm]⟩
  loopless := ⟨by
    intro u h
    rcases u with x | ⟨b, j⟩ <;>
      simp_all⟩
}
