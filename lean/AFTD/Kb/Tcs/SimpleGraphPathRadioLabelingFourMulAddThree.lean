import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsMultiRadioLabeling
import AFTD.Kb.Tcs.MultiLabelSpan
import AFTD.Kb.Tcs.SimpleGraphPathGraphDistGe
import AFTD.Kb.Tcs.PathRadioLabelFourMulAddThreeSep
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# simple_graph_path_radio_labeling_four_mul_add_three

Topic: graphs   Node: 1022dfe8d978

Provenance: helper lemma. for simple_graph_multi_radio_number_path_three_lt (RT-4, OP-384); pattern read off CP-SAT solutions (exp 1952), checked for m <= 40 (exp 1953)

For m >= 1, the labeling of the path P_{4m+3} that gives an odd vertex v the labels v, v+4, ..., v+4(m-1) and an even vertex v the labels 2((v/2) mod 2) + 4a for a < v/4 and 2((v/2) mod 2) + 4a + 4m for v/4 <= a < m is an (m,3)-radio labeling of span at most 8m - 2. So the threshold 4m + 4 for the value 8m - 1 is sharp.
-/

theorem simple_graph_path_radio_labeling_four_mul_add_three (m : ℕ) (hm : 1 ≤ m) :
    simple_graph_is_multi_radio_labeling (SimpleGraph.pathGraph (4 * m + 3)) m 3
        (fun v => if v.val % 2 = 1 then (Finset.range m).image (fun a => v.val + 4 * a)
          else (Finset.range m).image
            (fun a => 2 * (v.val / 2 % 2) + 4 * a + if a < v.val / 4 then 0 else 4 * m)) ∧
      multi_label_span (fun v : Fin (4 * m + 3) =>
        if v.val % 2 = 1 then (Finset.range m).image (fun a => v.val + 4 * a)
          else (Finset.range m).image
            (fun a => 2 * (v.val / 2 % 2) + 4 * a + if a < v.val / 4 then 0 else 4 * m)) ≤ 8 * m - 2 := by
  refine ⟨⟨fun v => ?_, fun x y a ha b hb hne => ?_⟩, ?_⟩
  · dsimp only
    split_ifs with hv
    · rw [Finset.card_image_of_injective _ (fun a b h => by omega)]
      exact Finset.card_range m
    · rw [Finset.card_image_of_injective _ (fun a b h => by
        split_ifs at h <;> omega)]
      exact Finset.card_range m
  · have hd := simple_graph_path_graph_dist_ge x y
    have hx := x.isLt
    have hy := y.isLt
    have hne' : x = y → a ≠ b := fun h1 h2 => hne (by rw [h1, h2])
    have hne'' : (x : ℕ) ≠ (y : ℕ) ∨ a ≠ b := by
      by_cases h : (x : ℕ) = (y : ℕ)
      · exact Or.inr (hne' (Fin.ext h))
      · exact Or.inl h
    clear hne' hne
    suffices h : (4 : ℤ) - |((x : ℕ) : ℤ) - ((y : ℕ) : ℤ)| ≤ |(a : ℤ) - b| by
      push_cast; linarith
    clear hd
    dsimp only at ha hb
    split_ifs at ha hb with h1 h2 h2 <;>
    · simp only [Finset.mem_image, Finset.mem_range] at ha hb
      obtain ⟨a', ha', rfl⟩ := ha
      obtain ⟨b', hb', rfl⟩ := hb
      have hne3 : (x : ℕ) ≠ (y : ℕ) ∨ a' ≠ b' := by
        rcases hne'' with h | h
        · exact Or.inl h
        · by_cases hxy : (x : ℕ) = (y : ℕ)
          · right; rintro rfl; apply h; (try split_ifs) <;> omega
          · exact Or.inl hxy
      have := path_radio_label_four_mul_add_three_sep m x y a' b' hx hy ha' hb' hne3
      simpa [h1, h2] using this
  · apply Finset.sup_le; intro x _; apply Finset.sup_le; intro y _
    apply Finset.sup_le; intro a ha; apply Finset.sup_le; intro b hb
    have hy := y.isLt
    dsimp only at hb
    split_ifs at hb with h2 <;> simp only [Finset.mem_image, Finset.mem_range] at hb <;>
      obtain ⟨b', hb', rfl⟩ := hb <;> (try split_ifs) <;> omega
