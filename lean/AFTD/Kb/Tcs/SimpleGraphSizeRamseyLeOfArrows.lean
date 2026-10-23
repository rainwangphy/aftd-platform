import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphSizeRamsey
import AFTD.Kb.Tcs.SimpleGraphSizeRamseyArrows

/-!
# simple_graph_size_ramsey_le_of_arrows

Topic: graphs   Node: 2d74a65e0deb

Provenance: helper lemma. sanity lemma for simple_graph_size_ramsey

Sanity: if G → (F, H) then r̂(F, H) ≤ e(G).
-/

theorem simple_graph_size_ramsey_le_of_arrows {α β : Type*} (F : SimpleGraph α) (H : SimpleGraph β)
    (k : ℕ) (G : SimpleGraph (Fin k)) (hG : simple_graph_size_ramsey_arrows G F H) :
    simple_graph_size_ramsey F H ≤ G.edgeSet.ncard :=
  Nat.sInf_le ⟨k, G, rfl, hG⟩
