import AFTD.Prelude
import AFTD.Kb.Tcs.MultiLabelSpan

/-!
# multi_label_span_sanity

Topic: graphs   Node: 960313a66446

Provenance: helper lemma. sanity check for multi_label_span (PR-281)

Sanity check: labels {0, 4} and {2} have span 4.
-/

theorem multi_label_span_sanity :
    multi_label_span (fun i : Fin 2 => if i = 0 then ({0, 4} : Finset ℕ) else {2}) = 4 := by decide
