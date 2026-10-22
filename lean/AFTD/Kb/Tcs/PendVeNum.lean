import AFTD.Prelude
import AFTD.Kb.Tcs.VeDominatesInside

/-!
# pend_ve_num

Topic: graphs   Node: 38077424fa9a

Provenance: helper lemma. step towards not_is_fix_v0_of_neighbors_unreachable

a_C is the minimum cardinality of a vertex set A' contained in the component part C such that A' together with v ve-dominates the induced subgraph on C together with v.
-/

/-- The minimum size of a set `S ⊆ A` such that `S ∪ {v}` ve-dominates all edges inside `A ∪ {v}`; the paper's pendant parameter `a_C`. -/
noncomputable def pend_ve_num {V : Type*} [Fintype V] (G : SimpleGraph V) (A : Set V) (v : V) : ℕ := sInf {k : ℕ | ∃ S : Finset V, (S : Set V) ⊆ A ∧
    ve_dominates_inside G ((S : Set V) ∪ {v}) (A ∪ {v}) ∧ S.card = k}
