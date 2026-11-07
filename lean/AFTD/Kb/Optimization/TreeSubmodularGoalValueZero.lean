import AFTD.Prelude
import AFTD.Kb.Optimization.StochasticMstSubmodularGoalValue
import AFTD.Kb.Optimization.PartialAssignmentLe
import AFTD.Kb.Optimization.IsMstCertificate
import AFTD.Kb.Optimization.IsMstFor
import AFTD.Kb.Optimization.IsSubmodularGoalFunction

/-!
# tree_submodular_goal_value_zero

Topic: submodular   Node: dc219c2996dc

Provenance: helper lemma. scout/2610-40844-stochastic-minimum-spanning-tree-identification-with-binary.md:703

For every finite simple graph G on a vertex type V that is a tree (G.IsTree), the submodular goal value stochastic_mst_submodular_goal_value G is 0.
-/

open scoped Classical in
theorem tree_submodular_goal_value_zero_subgraph_eq {V : Type*} [Fintype V] {G T' : SimpleGraph V}
    (hG : G.IsTree) (hT' : T'.IsTree) (hle : T' ≤ G) : T' = G := by
  have hcardG := hG.card_edgeFinset
  have hcardT' := hT'.card_edgeFinset
  have hcard_eq : T'.edgeFinset.card = G.edgeFinset.card := by omega
  have hsub : T'.edgeFinset ⊆ G.edgeFinset := by rwa [SimpleGraph.edgeFinset_subset_edgeFinset]
  have heq : T'.edgeFinset = G.edgeFinset :=
    Finset.eq_of_subset_of_card_le hsub (ge_of_eq hcard_eq)
  rwa [SimpleGraph.edgeFinset_inj] at heq

open scoped Classical in
theorem tree_submodular_goal_value_zero_is_mst_for {V : Type*} [Fintype V] (G : SimpleGraph V) (hG : G.IsTree)
    (α : G.edgeSet → Bool) : is_mst_for G G α := by
  refine ⟨le_rfl, hG, fun T' hT'le hT'tree => ?_⟩
  have heq : T' = G := tree_submodular_goal_value_zero_subgraph_eq hG hT'tree hT'le
  subst heq
  rfl

open scoped Classical in
theorem tree_submodular_goal_value_zero_is_mst_certificate {V : Type*} [Fintype V] (G : SimpleGraph V) (hG : G.IsTree)
    (β : G.edgeSet → Option Bool) : is_mst_certificate G β :=
  ⟨G, le_rfl, hG, fun α _ => tree_submodular_goal_value_zero_is_mst_for G hG α⟩

open scoped Classical in
theorem tree_submodular_goal_value_zero_is_submodular_goal_function {V : Type*} [Fintype V] (G : SimpleGraph V) (hG : G.IsTree) :
    is_submodular_goal_function G (fun _ => 0) 0 := by
  refine ⟨rfl, fun _ _ _ => le_rfl, fun _ _ _ _ _ _ => le_rfl, fun β => ?_⟩
  simp [tree_submodular_goal_value_zero_is_mst_certificate G hG β]

open scoped Classical in
/-- For a tree, the submodular goal value is 0. -/
theorem tree_submodular_goal_value_zero {V : Type*} [Fintype V] (G : SimpleGraph V) (hG : G.IsTree) :
    stochastic_mst_submodular_goal_value G = 0 := by
  change sInf {Q | ∃ g, is_submodular_goal_function G g Q} = 0
  exact Nat.sInf_eq_zero.mpr (Or.inl ⟨fun _ => 0, tree_submodular_goal_value_zero_is_submodular_goal_function G hG⟩)
