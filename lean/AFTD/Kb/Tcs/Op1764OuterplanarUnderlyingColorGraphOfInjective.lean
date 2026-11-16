import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsOuterplanar
import AFTD.Kb.Tcs.SimpleGraphUnderlyingColorGraph
import AFTD.Kb.Tcs.SimpleGraphIsMinor
import AFTD.Kb.Tcs.G

/-!
# op_1764_outerplanar_underlying_color_graph_of_injective

Topic: graphs   Node: 2ee204882470

Provenance: helper lemma. arXiv:2611.18391

For every finite outerplanar simple graph G on type V in the sense of simple_graph_is_outerplanar G and every injective vertex coloring c : V → ℕ, the underlying color graph simple_graph_underlying_color_graph G c on Set.range c is outerplanar in the sense of simple_graph_is_outerplanar.
-/

noncomputable def op_1764_color_equiv {V α : Type*} (c : V → α) (hinj : Function.Injective c) :
    V ≃ Set.range c := Equiv.ofInjective c hinj

noncomputable def op_1764_color_graph_iso {V α : Type*} (G : SimpleGraph V) (c : V → α)
    (hinj : Function.Injective c) :
    G ≃g simple_graph_underlying_color_graph G c where
  toEquiv := op_1764_color_equiv c hinj
  map_rel_iff' := by
    intro x y
    dsimp [simple_graph_underlying_color_graph]
    have heq : Set.rangeFactorization c = (op_1764_color_equiv c hinj).toEmbedding := rfl
    rw [heq]
    exact SimpleGraph.map_adj_apply

noncomputable def op_1764_induceIso {V W : Type*} (G : SimpleGraph V) (G' : SimpleGraph W)
    (iso : G ≃g G') (s : Set W) : G.induce (iso ⁻¹' s) ≃g G'.induce s where
  toEquiv := Equiv.subtypeEquiv iso.toEquiv (by intro x; simp)
  map_rel_iff' := by
    intro ⟨x, hx⟩ ⟨y, hy⟩
    dsimp [SimpleGraph.induce]
    exact iso.map_rel_iff

lemma op_1764_minor_of_iso {U V W : Type*} (H : SimpleGraph U) (G : SimpleGraph V) (G' : SimpleGraph W)
    (iso : G ≃g G') (h : simple_graph_is_minor H G') : simple_graph_is_minor H G := by
  rcases h with ⟨B', hconn, hdisj, hadj⟩
  refine ⟨fun u => iso ⁻¹' (B' u), ?_, ?_, ?_⟩
  · intro u
    have h_iso := op_1764_induceIso G G' iso (B' u)
    exact h_iso.connected_iff.mpr (hconn u)
  · intro u v hne
    exact (hdisj u v hne).preimage iso
  · intro u v hadj_uv
    rcases hadj u v hadj_uv with ⟨x', hx', y', hy', hadj_xy⟩
    refine ⟨iso.symm x', ?_, iso.symm y', ?_, ?_⟩
    · simp only [Set.mem_preimage, RelIso.apply_symm_apply, hx']
    · simp only [Set.mem_preimage, RelIso.apply_symm_apply, hy']
    · rwa [← iso.map_rel_iff, RelIso.apply_symm_apply, RelIso.apply_symm_apply]

/-- The underlying color graph of an injective coloring of an outerplanar graph is outerplanar. -/
theorem op_1764_outerplanar_underlying_color_graph_of_injective
    {V : Type*} [Fintype V] (G : SimpleGraph V)
    (houter : simple_graph_is_outerplanar G) (c : V → ℕ)
    (hinj : Function.Injective c) :
    simple_graph_is_outerplanar (simple_graph_underlying_color_graph G c) := by
  have iso := op_1764_color_graph_iso G c hinj
  constructor
  · intro hminor
    exact houter.1 (op_1764_minor_of_iso _ G _ iso hminor)
  · intro hminor
    exact houter.2 (op_1764_minor_of_iso _ G _ iso hminor)
