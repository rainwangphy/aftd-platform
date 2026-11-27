import AFTD.Prelude
import AFTD.Kb.Tcs.Op309CanonicalPaddedPortClasses
import AFTD.Kb.Tcs.Op309SelectedEdgeGraph

/-!
# op309_injective_padded_ports_canonical

Topic: graphs   Node: e5c1fe7ff093

Provenance: helper lemma. Sanity check for op309_canonical_padded_port_classes.

If the port map is injective on original edges, then it makes no extra identification of unselected edge ports.
-/

theorem op309_injective_padded_ports_canonical
    {V A : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (R : Finset G.edgeSet)
    (q : Sum G.edgeSet (V × Fin 3) → A)
    (hinj : Function.Injective (fun e : G.edgeSet => q (.inl e))) :
    op309_canonical_padded_port_classes G R q := by
  intro e f he hf hq
  have h : e = f := hinj hq
  subst f
  exact Relation.ReflTransGen.refl
