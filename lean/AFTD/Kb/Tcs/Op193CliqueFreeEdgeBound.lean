import AFTD.Prelude

/-!
# op_193_clique_free_edge_bound

Topic: graphs   Node: de450027fbb3

Provenance: helper lemma. Mathlib clique-free extremal graph bound.

A finite graph with no (r+1)-clique, where r is positive, has at most (r-1)n²/(2r) edges, expressed without division.
-/

open scoped BigOperators
open SimpleGraph

theorem op_193_clique_free_edge_bound {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (r : ℕ) (hr : 0 < r)
    (hfree : G.CliqueFree (r+1)) :
    2*r*G.edgeFinset.card ≤ (r-1)*(Fintype.card V)^2 := by
  obtain ⟨H, hd, hmax⟩ := exists_isTuranMaximal (V := V) hr
  letI : DecidableRel H.Adj := hd
  have hle : G.edgeFinset.card ≤ H.edgeFinset.card := hmax.2 hfree
  have heq : H.edgeFinset.card = (turanGraph (Fintype.card V) r).edgeFinset.card :=
    ((isTuranMaximal_iff_nonempty_iso_turanGraph hr).mp hmax).some.card_edgeFinset_eq
  calc
    2*r*G.edgeFinset.card ≤ 2*r*H.edgeFinset.card := Nat.mul_le_mul_left _ hle
    _ = 2*r*(turanGraph (Fintype.card V) r).edgeFinset.card := by rw [heq]
    _ ≤ (r-1)*(Fintype.card V)^2 := mul_card_edgeFinset_turanGraph_le
