import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ArrowsUnmarked
import AFTD.Kb.GameTheoryEconomics.ArrowsIsSource
import AFTD.Kb.GameTheoryEconomics.ArrowsIsSink
import AFTD.Kb.GameTheoryEconomics.ArrowsPos

/-!
# arrows_legal_move_degree_ne_one

Topic: combinatorial_games   Node: 46badb4f19c7

Provenance: helper lemma. Helper for arrows_parity_of_threads_le_two, arXiv:2610.15145 Theorem 10.3 / Corollary 10.4 (the induction in the proof of Theorem 10.3: every option has value (e-1) mod 2 or an option of value e mod 2), done directly on positions of T without the sum decomposition

If marking the unmarked edge uv as u -> v leaves u not a source and v not a sink, then neither u nor v has degree 1 (pendant edges can never be marked).
-/

theorem arrows_legal_move_degree_ne_one {V : Type*} [DecidableEq V] [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {p q : ArrowsPos V} {u v : V}
    (hu : ArrowsUnmarked G p u v) (hq : ∀ x y, q.1 x y = if x = u ∧ y = v then true else p.1 x y)
    (hsu : ¬ ArrowsIsSource G q u) (hsv : ¬ ArrowsIsSink G q v) :
    G.degree u ≠ 1 ∧ G.degree v ≠ 1 := by
  have hquv : q.1 u v = true := by rw [hq]; simp
  constructor
  · intro h1
    apply hsu
    refine ⟨by omega, fun w hw => ?_⟩
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (by rw [SimpleGraph.card_neighborFinset_eq_degree]; exact h1 :
      (G.neighborFinset u).card = 1)
    have hv : v ∈ G.neighborFinset u := by simpa using hu.1
    have hw' : w ∈ G.neighborFinset u := by simpa using hw
    rw [ha, Finset.mem_singleton] at hv hw'
    rw [hw', ← hv]; exact hquv
  · intro h1
    apply hsv
    refine ⟨by omega, fun w hw => ?_⟩
    obtain ⟨a, ha⟩ := Finset.card_eq_one.mp (by rw [SimpleGraph.card_neighborFinset_eq_degree]; exact h1 :
      (G.neighborFinset v).card = 1)
    have hv : u ∈ G.neighborFinset v := by simpa using hu.1.symm
    have hw' : w ∈ G.neighborFinset v := by simpa using hw
    rw [ha, Finset.mem_singleton] at hv hw'
    rw [hw', ← hv]; exact hquv
