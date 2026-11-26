import AFTD.Prelude
import AFTD.Kb.Tcs.Supp

/-!
# induced_component_ambient_vertex_properties

Topic: graphs   Node: 3237e01705ea

Provenance: helper lemma. Component transfer for OP-1957; https://arxiv.org/abs/2611.22690.

Components of an induced graph map injectively to disjoint, anticomplete ambient vertex sets with preserved cardinalities.
-/

noncomputable def in1206_component_vertices
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (R : Set V)
    (c : (G.induce R).ConnectedComponent) : Finset V := by
  classical
  exact c.supp.toFinset.map ⟨Subtype.val, Subtype.val_injective⟩

theorem induced_component_ambient_vertex_properties
    {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) (R : Set V)
    (c d : (G.induce R).ConnectedComponent) :
    (in1206_component_vertices G R c : Set V) ⊆ R ∧
    (in1206_component_vertices G R c).card = c.supp.ncard ∧
    (c ≠ d → Disjoint (in1206_component_vertices G R c)
      (in1206_component_vertices G R d)) ∧
    (∀ u ∈ in1206_component_vertices G R c, ∀ v ∈ R,
      v ∉ in1206_component_vertices G R c → ¬ G.Adj u v) := by
  classical
  let H := G.induce R
  constructor
  · intro v hv
    change v ∈ c.supp.toFinset.map ⟨Subtype.val, Subtype.val_injective⟩ at hv
    obtain ⟨u,_,rfl⟩ := Finset.mem_map.mp hv
    exact u.property
  constructor
  · change (c.supp.toFinset.map ⟨Subtype.val, Subtype.val_injective⟩).card = c.supp.ncard
    rw [Finset.card_map, ← Set.ncard_eq_toFinset_card']
  constructor
  · intro hcd
    apply Finset.disjoint_left.mpr
    intro v hvc hvd
    change v ∈ c.supp.toFinset.map ⟨Subtype.val, Subtype.val_injective⟩ at hvc
    change v ∈ d.supp.toFinset.map ⟨Subtype.val, Subtype.val_injective⟩ at hvd
    obtain ⟨u,hu,huv⟩ := Finset.mem_map.mp hvc
    obtain ⟨w,hw,hwv⟩ := Finset.mem_map.mp hvd
    have huw : u = w := Subtype.ext (huv.trans hwv.symm)
    have huc : u ∈ c.supp := Set.mem_toFinset.mp hu
    have hwd : w ∈ d.supp := Set.mem_toFinset.mp hw
    exact Set.disjoint_left.mp (SimpleGraph.pairwise_disjoint_supp_connectedComponent H hcd)
      (huw ▸ huc) hwd
  · intro u hu v hv hvnot huv
    change u ∈ c.supp.toFinset.map ⟨Subtype.val, Subtype.val_injective⟩ at hu
    obtain ⟨u',hu',rfl⟩ := Finset.mem_map.mp hu
    let v' : R := ⟨v,hv⟩
    have huC : u' ∈ c.supp := Set.mem_toFinset.mp hu'
    have hadj : (G.induce R).Adj u' v' := huv
    have hvC : v' ∈ c.supp := (c.mem_supp_congr_adj hadj).mp huC
    apply hvnot
    change v ∈ c.supp.toFinset.map ⟨Subtype.val, Subtype.val_injective⟩
    exact Finset.mem_map.mpr ⟨v',Set.mem_toFinset.mpr hvC,rfl⟩
