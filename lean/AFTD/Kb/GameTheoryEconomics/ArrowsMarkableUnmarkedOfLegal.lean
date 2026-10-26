import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ArrowsMarkableUnmarked
import AFTD.Kb.GameTheoryEconomics.ArrowsLegalMove
import AFTD.Kb.GameTheoryEconomics.ArrowsLegalMoveDegreeNeOne
import AFTD.Kb.GameTheoryEconomics.ArrowsIsSource
import AFTD.Kb.GameTheoryEconomics.ArrowsIsSink
import AFTD.Kb.GameTheoryEconomics.ArrowsPos
import AFTD.Kb.GameTheoryEconomics.ArrowsUnmarked

/-!
# arrows_markable_unmarked_of_legal

Topic: combinatorial_games   Node: 2ceb5869fce5

Provenance: helper lemma. Helper for arrows_parity_of_threads_le_two, arXiv:2610.15145 Theorem 10.3 / Corollary 10.4 (the induction in the proof of Theorem 10.3: every option has value (e-1) mod 2 or an option of value e mod 2), done directly on positions of T without the sum decomposition

Every legal move of the Game of Arrows decreases the number of unmarked markable edges by exactly one.
-/

theorem arrows_markable_unmarked_of_legal {V : Type*} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (p q : ArrowsPos V) (h : ArrowsLegalMove G p q) :
    arrows_markable_unmarked G q + 1 = arrows_markable_unmarked G p := by
  classical
  obtain ⟨u, v, hu, hq, -, hsu, hsv, -⟩ := h
  obtain ⟨hdu, hdv⟩ := arrows_legal_move_degree_ne_one G hu hq hsu hsv
  unfold arrows_markable_unmarked
  have hmem : s(u, v) ∈ G.edgeFinset.filter (fun e => (∀ w ∈ e, G.degree w ≠ 1) ∧
      e.lift ⟨fun a b => p.1 a b = false ∧ p.1 b a = false, fun _ _ => propext and_comm⟩) := by
    simp only [Finset.mem_filter, SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, Sym2.lift_mk]
    refine ⟨hu.1, ?_, by simpa using hu.2.1, by simpa using hu.2.2⟩
    intro w hw; rcases Sym2.mem_iff.mp hw with rfl | rfl <;> assumption
  rw [← Finset.card_erase_add_one hmem]
  congr 2
  ext e
  induction e using Sym2.ind with
  | _ a b =>
  simp only [Finset.mem_erase, Finset.mem_filter, SimpleGraph.mem_edgeFinset,
    SimpleGraph.mem_edgeSet, Sym2.lift_mk, hq]
  constructor
  · rintro ⟨hab, hd, h1, h2⟩
    refine ⟨?_, hab, hd, ?_, ?_⟩
    · rintro hs
      rcases Sym2.eq_iff.mp hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> simp_all
    · by_cases hc : a = u ∧ b = v <;> simp_all
    · by_cases hc : b = u ∧ a = v <;> simp_all
  · rintro ⟨hne, hab, hd, h1, h2⟩
    have hn1 : ¬ (a = u ∧ b = v) := by rintro ⟨rfl, rfl⟩; exact hne rfl
    have hn2 : ¬ (b = u ∧ a = v) := by rintro ⟨rfl, rfl⟩; exact hne Sym2.eq_swap
    refine ⟨hab, hd, ?_, ?_⟩ <;> simp [hn1, hn2, h1, h2]
