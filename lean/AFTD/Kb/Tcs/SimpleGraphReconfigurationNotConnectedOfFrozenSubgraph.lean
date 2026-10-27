import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphReconfigurationFrozenCoreReachableEq
import AFTD.Kb.Tcs.SimpleGraphReconfigurationGraph

/-!
# simple_graph_reconfiguration_not_connected_of_frozen_subgraph

Topic: graphs   Node: 85a624748e5e

Provenance: helper lemma. step towards frozen_obstruction_lifting_blowup

If a simple graph G admits a proper ℓ-coloring α whose restriction to a nonempty subset S is frozen with respect to all ℓ colors, and G also admits a proper (ℓ - 1)-coloring β, then the ℓ-reconfiguration graph of G is disconnected.
-/

/-- A graph with a coloring frozen on a nonempty core and another coloring with fewer colors has a disconnected reconfiguration graph. -/
theorem simple_graph_reconfiguration_not_connected_of_frozen_subgraph
    {V : Type*} (G : SimpleGraph V) (ℓ : ℕ) (hℓ : 1 ≤ ℓ)
    (S : Set V) (hS : S.Nonempty)
    (α : G.Coloring (Fin ℓ))
    (hfrozen : ∀ x ∈ S, ∀ i : Fin ℓ, α x = i ∨ ∃ y ∈ S, G.Adj x y ∧ α y = i)
    (β : G.Coloring (Fin (ℓ - 1))) :
    ¬ (simple_graph_reconfiguration_graph G ℓ).Connected := by
  intro hconn
  let β' : G.Coloring (Fin ℓ) :=
    SimpleGraph.Coloring.mk (fun v => Fin.castLE (Nat.sub_le ℓ 1) (β v))
      (fun hvw h => β.valid hvw (Fin.castLE_injective _ h))
  have hreach : (simple_graph_reconfiguration_graph G ℓ).Reachable α β' :=
    hconn.preconnected α β'
  have heq : ∀ x ∈ S, β' x = α x :=
    simple_graph_reconfiguration_frozen_core_reachable_eq G S α β' hfrozen hreach
  rcases hS with ⟨x₀, hx₀⟩
  let last_col : Fin ℓ := ⟨ℓ - 1, by omega⟩
  rcases hfrozen x₀ hx₀ last_col with hx | ⟨y, hy, -, hycol⟩
  · have h1 : β' x₀ = last_col := by rw [heq x₀ hx₀, hx]
    have h2 : (β' x₀).1 = ℓ - 1 := congrArg Fin.val h1
    have h3 : (β' x₀).1 < ℓ - 1 := (β x₀).isLt
    omega
  · have h1 : β' y = last_col := by rw [heq y hy, hycol]
    have h2 : (β' y).1 = ℓ - 1 := congrArg Fin.val h1
    have h3 : (β' y).1 < ℓ - 1 := (β y).isLt
    omega
