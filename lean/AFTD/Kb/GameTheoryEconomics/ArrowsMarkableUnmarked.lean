import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ArrowsPos

/-!
# arrows_markable_unmarked

Topic: combinatorial_games   Node: 888d9dc2540c

Provenance: helper lemma. Helper for arrows_parity_of_threads_le_two, arXiv:2610.15145 Theorem 10.3 / Corollary 10.4 (the induction in the proof of Theorem 10.3: every option has value (e-1) mod 2 or an option of value e mod 2), done directly on positions of T without the sum decomposition

The number of unmarked markable edges of a position p of the Game of Arrows on G: edges of G neither of whose endpoints has degree 1 and that carry no arrow in p.
-/

open scoped Classical in
noncomputable def arrows_markable_unmarked {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (p : ArrowsPos V) : ℕ :=
  (G.edgeFinset.filter (fun e => (∀ v ∈ e, G.degree v ≠ 1) ∧
    e.lift ⟨fun u v => p.1 u v = false ∧ p.1 v u = false, fun _ _ => propext and_comm⟩)).card
