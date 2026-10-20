import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphMultiRadioNumber
import AFTD.Kb.Tcs.SimpleGraphIsMultiRadioLabeling
import AFTD.Kb.Tcs.MultiLabelSpan
import AFTD.Kb.Tcs.PathRadioLabelEightMulSep
import AFTD.Kb.Tcs.SimpleGraphPathGraphDistGe
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# simple_graph_multi_radio_number_path_le_eight_mul

Topic: graphs   Node: a7dab7bfe85a

Provenance: formalization of a published result. Source: arXiv:2610.25863 (On Multi-label radio Labelings of Graphs), Proposition 4.4

For n, m >= 1 the (m,3)-radio number of the path P_n is at most 8m - 1.
-/

theorem simple_graph_multi_radio_number_path_le_eight_mul (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) :
    simple_graph_multi_radio_number (SimpleGraph.pathGraph n) m 3 ≤ 8 * m - 1 := by
  have hf : simple_graph_is_multi_radio_labeling (SimpleGraph.pathGraph n) m 3
      (fun v => (Finset.range m).image (fun a => 8 * a + 3 * v.val % 8)) := by
    refine ⟨fun v => ?_, fun x y a ha b hb hne => ?_⟩
    · rw [Finset.card_image_of_injective _ (fun a b h => by omega)]
      exact Finset.card_range m
    · have hd := simple_graph_path_graph_dist_ge x y
      simp only [Finset.mem_image, Finset.mem_range] at ha hb
      obtain ⟨a', ha', rfl⟩ := ha
      obtain ⟨b', hb', rfl⟩ := hb
      have hne3 : (x : ℕ) ≠ (y : ℕ) ∨ a' ≠ b' := by
        by_cases hxy : (x : ℕ) = (y : ℕ)
        · right; rintro rfl; exact hne (by rw [Fin.ext hxy])
        · exact Or.inl hxy
      have := path_radio_label_eight_mul_sep x y a' b' hne3
      push_cast at this ⊢
      linarith
  have hs : multi_label_span (fun v : Fin n => (Finset.range m).image (fun a => 8 * a + 3 * v.val % 8))
      ≤ 8 * m - 1 := by
    apply Finset.sup_le; intro x _; apply Finset.sup_le; intro y _
    apply Finset.sup_le; intro a ha; apply Finset.sup_le; intro b hb
    simp only [Finset.mem_image, Finset.mem_range] at hb
    obtain ⟨b', hb', rfl⟩ := hb
    omega
  exact le_trans (Nat.sInf_le ⟨_, hf, rfl⟩) hs
