import AFTD.Prelude

/-!
# not_op_1952_cubic_bipartite_card_ge_six

Topic: graphs   Node: e94e093af737

Provenance: original. Related work: refutes `op_1952_cubic_bipartite_card_ge_six`

The statement `op_1952_cubic_bipartite_card_ge_six` is false: The statement is false for the empty vertex set. On `ULift Empty`, the bottom graph has no vertices, so `IsRegularOfDegree 3` holds vacuously and `Colorable 2` holds, but `Fintype.card (ULift Empty) = 0`, contradicting `6 ≤ 0`. The intended theorem needs a nonempty-vertex hypothesis (or `0 < Fintype.card V`).
-/

theorem not_op_1952_cubic_bipartite_card_ge_six : ¬ (∀ {V : Type*} [Fintype V] (G : SimpleGraph V)
    [G.LocallyFinite] (hreg : G.IsRegularOfDegree 3) (hbip : G.Colorable 2), 6 ≤ Fintype.card V) := by
  intro h
  have hreg : (⊥ : SimpleGraph (ULift Empty)).IsRegularOfDegree 3 := by
    intro v
    exact v.down.elim
  have hcol : (⊥ : SimpleGraph (ULift Empty)).Colorable 2 :=
    SimpleGraph.Colorable.of_isEmpty 2
  have hle := h (V := ULift Empty) (⊥ : SimpleGraph (ULift Empty)) hreg hcol
  have hcard : Fintype.card (ULift Empty) = 0 := by simp
  omega
