import AFTD.Prelude
import AFTD.Kb.Tcs.EdgeListConnectedCubic
import AFTD.Kb.Tcs.EdgeListHColorable
import AFTD.Kb.Tcs.PetersenGraph

/-!
# petersen_colorable_of_three_edge_colorable

Topic: np_completeness   Node: 50c11521a0e6

Provenance: formalization of a published result. Source: arXiv:2610.35794 (Computational complexity of the H-coloring problem in cubic graphs), Sec. 3 (H-coloring for 3-edge-colorable H reduces to 3-edge-coloring, via Lemma 1(A) from its ref. [8]); here the easy direction for H = P10: map the three colors to the three edges at one vertex of P10

If es is an edge list with edge_list_connected_cubic n es that has a proper 3-edge-coloring c : Fin es.length → Fin 3 (any two distinct edges i ≠ j sharing an endpoint get different colors), then it has a Petersen coloring: edge_list_h_colorable petersen_graph n es.
-/

theorem petersen_colorable_of_three_edge_colorable (n : ℕ) (es : List (ℕ × ℕ))
    (hG : edge_list_connected_cubic n es)
    (hc : ∃ c : Fin es.length → Fin 3, ∀ i j : Fin es.length, i ≠ j →
      (es[i].1 = es[j].1 ∨ es[i].1 = es[j].2 ∨ es[i].2 = es[j].1 ∨ es[i].2 = es[j].2) → c i ≠ c j) :
    edge_list_h_colorable petersen_graph n es := by
  obtain ⟨c, hc⟩ := hc
  obtain ⟨-, hdeg, -⟩ := hG
  letI : DecidableRel petersen_graph.Adj := fun s t => inferInstanceAs (Decidable (Disjoint s.1 t.1))
  let x0 : {s : Finset (Fin 5) // s.card = 2} := ⟨{0, 1}, by decide⟩
  let y : Fin 3 → {s : Finset (Fin 5) // s.card = 2} :=
    ![⟨{2, 3}, by decide⟩, ⟨{2, 4}, by decide⟩, ⟨{3, 4}, by decide⟩]
  have hy : ∀ k, petersen_graph.Adj x0 (y k) := by decide
  have hy' : ∀ z, petersen_graph.Adj x0 z → ∃ k, z = y k := by decide
  refine ⟨fun i => ⟨s(x0, y (c i)), hy (c i)⟩, fun v hv => ⟨x0, ?_⟩⟩
  ext e
  constructor
  · rintro ⟨i, -, rfl⟩
    exact ⟨hy (c i), Sym2.mem_mk_left _ _⟩
  · rintro ⟨he, hx⟩
    obtain ⟨z, rfl⟩ := Sym2.mem_iff_exists.mp hx
    obtain ⟨k, rfl⟩ := hy' z he
    set S := Finset.univ.filter (fun i : Fin es.length => es[i].1 = v ∨ es[i].2 = v) with hS
    have hinj : Set.InjOn c S := by
      intro i hi j hj hij
      by_contra hne
      simp only [hS, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hi hj
      apply hc i j hne _ hij
      simp only [Fin.getElem_fin] at hi hj ⊢
      rcases hi with hi | hi <;> rcases hj with hj | hj <;> simp [hi, hj]
    have hcard : (S.image c).card = 3 := by rw [Finset.card_image_of_injOn hinj, hdeg v hv]
    have huniv : S.image c = Finset.univ := Finset.eq_univ_of_card _ (by simp [hcard])
    have hk : k ∈ S.image c := huniv ▸ Finset.mem_univ k
    obtain ⟨i, hiS, hik⟩ := Finset.mem_image.mp hk
    refine ⟨i, by simpa [hS] using hiS, ?_⟩
    simp [hik]
