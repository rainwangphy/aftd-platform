import AFTD.Prelude

/-!
# op309_k33_witness_min_degree

Topic: graphs   Node: 2784d8ef4fef

Provenance: helper lemma. Finite obstruction to a proposed greedy route via simple_graph_rich_neighbor_coloring_iff_witness_graph, experiment 30835.

In K3,3, every total edge-dominating witness set produces a witness conflict graph with minimum degree at least six; hence a four-degeneracy approach cannot prove five-colorability even in this example.
-/

set_option maxRecDepth 16384
set_option maxHeartbeats 4000000
set_option synthInstance.maxSize 100000

def op309_rook_adj (e f : Fin 3 × Fin 3) : Prop :=
  e ≠ f ∧ (e.1 = f.1 ∨ e.2 = f.2)

instance : DecidableRel op309_rook_adj := fun e f => by
  unfold op309_rook_adj
  infer_instance

def op309_rook_witness_adj (R : Finset (Fin 3 × Fin 3)) (e f : Fin 3 × Fin 3) : Prop :=
  e ≠ f ∧ (op309_rook_adj e f ∨
    ∃ r ∈ R, op309_rook_adj r e ∧ op309_rook_adj r f)

instance (R : Finset (Fin 3 × Fin 3)) : DecidableRel (op309_rook_witness_adj R) :=
  fun e f => by unfold op309_rook_witness_adj; infer_instance

theorem op309_rook_single_witness_degree :
    ∀ e r : Fin 3 × Fin 3, op309_rook_adj e r →
      6 ≤ (Finset.univ.filter (op309_rook_witness_adj {r} e)).card := by
  decide

theorem op309_k33_witness_min_degree (R : Finset (Fin 3 × Fin 3))
    (hdom : ∀ e, ∃ r ∈ R, op309_rook_adj e r) :
    ∀ e, 6 ≤ (Finset.univ.filter (op309_rook_witness_adj R e)).card := by
  intro e
  obtain ⟨r, hr, her⟩ := hdom e
  have hs : Finset.univ.filter (op309_rook_witness_adj {r} e) ⊆
      Finset.univ.filter (op309_rook_witness_adj R e) := by
    intro f hf
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hf ⊢
    rcases hf with ⟨hne, h | ⟨r', hr', h₁, h₂⟩⟩
    · exact ⟨hne, Or.inl h⟩
    · have : r' = r := by simpa using hr'
      subst r'
      exact ⟨hne, Or.inr ⟨r, hr, h₁, h₂⟩⟩
  have hc := Finset.card_le_card hs
  have hm := op309_rook_single_witness_degree e r her
  omega
