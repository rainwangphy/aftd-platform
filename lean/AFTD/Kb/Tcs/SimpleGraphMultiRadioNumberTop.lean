import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphMultiRadioNumber
import AFTD.Kb.Tcs.MultiLabelSpanGeOfRadioLabelingTop
import AFTD.Kb.Tcs.ExistsRadioLabelingTopSpanEq
import AFTD.Kb.Tcs.SimpleGraphIsMultiRadioLabeling
import AFTD.Kb.Tcs.MultiLabelSpan

/-!
# simple_graph_multi_radio_number_top

Topic: graphs   Node: 74993ff90121

Provenance: formalization of a published result. Source: arXiv:2610.25863 (On Multi-label radio Labelings of Graphs), Proposition 2.3

For n >= 2, k >= 1 and m >= 1, the (m,k)-radio number of the complete graph K_n is k(mn - 1).
-/

theorem simple_graph_multi_radio_number_top (n m k : ℕ) (hn : 2 ≤ n) (hk : 1 ≤ k) (hm : 1 ≤ m) :
    simple_graph_multi_radio_number (⊤ : SimpleGraph (Fin n)) m k = k * (m * n - 1) := by
  have _ := hm
  dsimp [simple_graph_multi_radio_number]
  rcases exists_radio_labeling_top_span_eq n m k hn hk with ⟨f, hf, hspan⟩
  apply le_antisymm
  · have hmem : multi_label_span f ∈ {s | ∃ f, simple_graph_is_multi_radio_labeling (⊤ : SimpleGraph (Fin n)) m k f ∧ multi_label_span f = s} :=
      ⟨f, hf, rfl⟩
    have hle := Nat.sInf_le hmem
    rwa [hspan] at hle
  · apply le_csInf
    · exact ⟨multi_label_span f, f, hf, rfl⟩
    · rintro b ⟨g, hg, rfl⟩
      exact multi_label_span_ge_of_radio_labeling_top n m k g hg
