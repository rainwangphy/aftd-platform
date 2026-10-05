import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsConnectedVertexSet

/-!
# poc8_not_connected_of_cut

Topic: fair_division   Node: adeca548ceb2

Cut criterion: if R contains a vertex a of S but misses a vertex b of S, and no edge of G leads from R into S outside R, then S does not induce a connected subgraph.
-/

theorem poc8_not_connected_of_cut {V : Type*} (G : SimpleGraph V) (S R : Set V) (a b : V)
    (ha : a ∈ S) (haR : a ∈ R) (hb : b ∈ S) (hbR : b ∉ R)
    (hcl : ∀ v w, v ∈ S → w ∈ R → G.Adj w v → v ∈ R) :
    ¬ is_connected_vertex_set G S := by
  intro hc
  obtain ⟨p⟩ := hc.preconnected ⟨a, ha⟩ ⟨b, hb⟩
  have key : ∀ (x y : S) (q : (G.induce S).Walk x y), (x : V) ∈ R → (y : V) ∈ R := by
    intro x y q
    induction q with
    | nil => exact id
    | cons h q ih => intro hx; exact ih (hcl _ _ (Subtype.prop _) hx h)
  exact hbR (key _ _ p haR)
