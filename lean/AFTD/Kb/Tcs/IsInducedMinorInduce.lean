import AFTD.Prelude
import AFTD.Kb.Tcs.IsInducedMinor

/-!
# is_induced_minor_induce

Topic: graphs   Node: f9bc6dc28589

Provenance: helper lemma. arXiv:2611.09627 Section 2

If H is an induced minor of G, then for any subset A of vertices of H, the induced subgraph H[A] is also an induced minor of G.
-/

/-- If H is an induced minor of G, then any induced subgraph of H is also an induced minor of G. -/
theorem is_induced_minor_induce {V_H V_G : Type*} (H : SimpleGraph V_H) (G : SimpleGraph V_G)
    (h_minor : is_induced_minor H G) (A : Set V_H) :
    is_induced_minor (H.induce A) G := by
  rcases h_minor with ⟨X, hconn, hdisj, hadj⟩
  refine ⟨fun v => X v.1, fun v => hconn v.1, ?_, ?_⟩
  · intro u v hne
    exact hdisj u.1 v.1 (Subtype.val_injective.ne hne)
  · intro u v hne
    rw [SimpleGraph.induce_adj]
    exact hadj u.1 v.1 (Subtype.val_injective.ne hne)
