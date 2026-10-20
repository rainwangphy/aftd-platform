import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphMultiRadioNumber
import AFTD.Kb.Tcs.SimpleGraphPathRadioLabelingFourMulAddThree
import AFTD.Kb.Tcs.SimpleGraphIsMultiRadioLabeling
import AFTD.Kb.Tcs.MultiLabelSpan

/-!
# simple_graph_multi_radio_number_path_three_lt

Topic: graphs   Node: 73e9151c7c2e

Provenance: original. Related work: arXiv:2610.25863 (On Multi-label radio Labelings of Graphs), Conjecture 1 (case k = 3): the conjecture leaves n0 unspecified

The threshold 4m + 4 is sharp: the (m,3)-radio number of P_{4m+3} is less than 8m - 1.
-/

theorem simple_graph_multi_radio_number_path_three_lt (m : ℕ) (hm : 1 ≤ m) :
    simple_graph_multi_radio_number (SimpleGraph.pathGraph (4 * m + 3)) m 3 < 8 * m - 1 := by
  obtain ⟨hf, hs⟩ := simple_graph_path_radio_labeling_four_mul_add_three m hm
  have h := Nat.sInf_le (show multi_label_span _ ∈ {s | ∃ f,
      simple_graph_is_multi_radio_labeling (SimpleGraph.pathGraph (4 * m + 3)) m 3 f ∧
        multi_label_span f = s} from ⟨_, hf, rfl⟩)
  unfold simple_graph_multi_radio_number
  omega
