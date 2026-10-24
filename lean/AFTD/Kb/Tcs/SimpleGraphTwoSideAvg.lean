import AFTD.Prelude

/-!
# simple_graph_two_side_avg

Topic: graphs   Node: a734e00c234f

Provenance: helper lemma. step towards simple_graph_avg_connected_induced_order_min_of_bridge

The pair value R(G,G',u,v) = (S+S'+P'Q+PQ')/(N+N'+PP'), where for each side N counts the nonempty vertex sets inducing a connected subgraph, S is the sum of their cardinalities, P counts those among them containing the distinguished endpoint, and Q the sum of their cardinalities.
-/

/-- Pair value of a bridge joining G at u to G' at v: (S+S'+P'Q+PQ')/(N+N'+PP') with per-side connected-subset counts. -/
noncomputable def simple_graph_two_side_avg {V W : Type*} [Fintype V] [Fintype W]
    [DecidableEq V] [DecidableEq W]
    (G : SimpleGraph V) (G' : SimpleGraph W) (u : V) (v : W) : ℚ := by
  classical
  let connV : Finset (Finset V) :=
    Finset.univ.filter (fun S => S.Nonempty ∧ (G.induce (S : Set V)).Connected)
  let connW : Finset (Finset W) :=
    Finset.univ.filter (fun S => S.Nonempty ∧ (G'.induce (S : Set W)).Connected)
  let N₁ : ℕ := connV.card
  let S₁ : ℕ := ∑ S ∈ connV, S.card
  let P₁ : ℕ := (connV.filter (fun S => u ∈ S)).card
  let Q₁ : ℕ := ∑ S ∈ connV.filter (fun S => u ∈ S), S.card
  let N₂ : ℕ := connW.card
  let S₂ : ℕ := ∑ S ∈ connW, S.card
  let P₂ : ℕ := (connW.filter (fun S => v ∈ S)).card
  let Q₂ : ℕ := ∑ S ∈ connW.filter (fun S => v ∈ S), S.card
  exact ((S₁ + S₂ + P₂ * Q₁ + P₁ * Q₂ : ℕ) : ℚ) / ((N₁ + N₂ + P₁ * P₂ : ℕ) : ℚ)
