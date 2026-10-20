import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsMultiRadioLabeling
import AFTD.Kb.Tcs.MultiLabelSpan

/-!
# simple_graph_multi_radio_number

Topic: graphs   Node: 3804d5799308

Provenance: formalization of a published result. Source: arXiv:2610.25863 (On Multi-label radio Labelings of Graphs), Sec. 1 (radio number)

The (m,k)-radio number lambda_k^m(G): the least span of an (m,k)-radio labeling of G.
-/

/-- The (m,k)-radio number lambda_k^m(G): the least span of an (m,k)-radio labeling of G. -/
noncomputable def simple_graph_multi_radio_number {V : Type*} [Fintype V] (G : SimpleGraph V)
    (m k : ℕ) : ℕ :=
  sInf {s | ∃ f, simple_graph_is_multi_radio_labeling G m k f ∧ multi_label_span f = s}
