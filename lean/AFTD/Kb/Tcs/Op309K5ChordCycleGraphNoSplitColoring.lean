import AFTD.Prelude
import AFTD.Kb.Tcs.Op309K5ChordCycleGraph
import AFTD.Kb.Tcs.SimpleGraphIsRichNeighborColoring
import AFTD.Kb.Tcs.SimpleGraphEdgeIsRich

/-!
# op309_k5_chord_cycle_graph_no_split_coloring

Topic: graphs   Node: 6ea370dfa8c8

Provenance: helper lemma. A prescribed-cycle obstruction to extending the three-plus-two chord construction in https://arxiv.org/abs/2611.24297; experiments 34597, 34600, and 34611.

For the displayed connected ten-vertex cubic graph and its specified Hamiltonian ten-cycle, no rich-neighbor five-coloring assigns all ten cycle edges to the first three colors and all five matching chords to the remaining two colors. The graph can still have a rich-neighbor five-coloring, and another Hamiltonian cycle can admit such a palette split.
-/

set_option maxRecDepth 32768
set_option maxHeartbeats 6000000

local instance  aftdLocal_b33884dbfa4565f3_0 : DecidableRel op309_k5_chord_cycle_graph.Adj := fun u v =>
  inferInstanceAs (Decidable
    (((u.val, v.val) ∈ ([(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(0,9),(0,3),(1,5),(2,7),(4,8),(6,9)] : List (ℕ × ℕ))) ∨
     ((v.val, u.val) ∈ ([(0,1),(1,2),(2,3),(3,4),(4,5),(5,6),(6,7),(7,8),(8,9),(0,9),(0,3),(1,5),(2,7),(4,8),(6,9)] : List (ℕ × ℕ)))))

local instance  aftdLocal_b33884dbfa4565f3_1 : DecidableRel op309_k5_chord_cycle_graph.lineGraph.Adj := fun e f =>
  decidable_of_iff (e ≠ f ∧ ∃ v : Fin 10, v ∈ e.1 ∧ v ∈ f.1)
    SimpleGraph.lineGraph_adj_iff_exists.symm

def op309_k5_chord_word : Fin 10 → Fin 5 := ![0,1,2,0,3,1,4,2,3,4]
def op309_k5_chord_first : Fin 5 → Fin 10 := ![0,1,2,4,6]
def op309_k5_chord_second : Fin 5 → Fin 10 := ![3,5,7,8,9]
def op309_k5_cycle_edge (i : Fin 10) : op309_k5_chord_cycle_graph.edgeSet :=
  ⟨s(i,i+1), by fin_cases i <;> decide⟩
def op309_k5_chord_edge (i : Fin 5) : op309_k5_chord_cycle_graph.edgeSet :=
  ⟨s(op309_k5_chord_first i,op309_k5_chord_second i), by fin_cases i <;> decide⟩
def op309_k5_chord_neighbors : Fin 5 → Fin 4 → Fin 10 :=
  ![![9,0,2,3], ![0,1,4,5], ![1,2,6,7], ![3,4,7,8], ![5,6,8,9]]

theorem op309_k5_chord_word_obstruction : ∀ c : Fin 5 → Fin 2, ∃ i : Fin 10,
  c (op309_k5_chord_word i) = c (op309_k5_chord_word (i+1)) ∧
  c (op309_k5_chord_word (i+2)) = c (op309_k5_chord_word (i+3)) := by decide

theorem op309_k5_cycle_chord_adj : ∀ i : Fin 10,
    op309_k5_chord_cycle_graph.lineGraph.Adj (op309_k5_cycle_edge i) (op309_k5_chord_edge (op309_k5_chord_word i)) ∧
    op309_k5_chord_cycle_graph.lineGraph.Adj (op309_k5_cycle_edge i) (op309_k5_chord_edge (op309_k5_chord_word (i+1))) ∧
    op309_k5_chord_edge (op309_k5_chord_word i) ≠ op309_k5_chord_edge (op309_k5_chord_word (i+1)) := by decide

theorem op309_k5_chord_neighbor_adj : ∀ a : Fin 5, ∀ k : Fin 4,
    op309_k5_chord_cycle_graph.lineGraph.Adj (op309_k5_chord_edge a) (op309_k5_cycle_edge (op309_k5_chord_neighbors a k)) := by decide

theorem op309_k5_chord_neighbor_injective : ∀ a : Fin 5, Function.Injective (fun k : Fin 4 => op309_k5_cycle_edge (op309_k5_chord_neighbors a k)) := by decide

theorem op309_k5_cycle_neighbor_exhaust : ∀ (i : Fin 10) (f : op309_k5_chord_cycle_graph.edgeSet),
    op309_k5_chord_cycle_graph.lineGraph.Adj (op309_k5_cycle_edge (i+1)) f ↔
    f = op309_k5_cycle_edge i ∨ f = op309_k5_cycle_edge (i+2) ∨
    f = op309_k5_chord_edge (op309_k5_chord_word (i+1)) ∨ f = op309_k5_chord_edge (op309_k5_chord_word (i+2)) := by decide

theorem op309_k5_chord_cycle_graph_no_split_coloring
    (c : op309_k5_chord_cycle_graph.lineGraph.Coloring (Fin 5))
    (hcycle : ∀ i, (c (op309_k5_cycle_edge i)).val < 3)
    (hchord : ∀ a, 3 ≤ (c (op309_k5_chord_edge a)).val) :
    ¬ simple_graph_is_rich_neighbor_coloring op309_k5_chord_cycle_graph c := by
  intro hrn
  let t (a : Fin 5) : Fin 2 := ⟨(c (op309_k5_chord_edge a)).val - 3, by
    have hlo := hchord a
    have hhi := (c (op309_k5_chord_edge a)).isLt
    omega⟩
  obtain ⟨i, hleft, hright⟩ := op309_k5_chord_word_obstruction t
  have same {a b : Fin 5} (h : t a = t b) :
      c (op309_k5_chord_edge a) = c (op309_k5_chord_edge b) := by
    apply Fin.ext
    have hv := congrArg Fin.val h
    have ha := hchord a
    have hb := hchord b
    dsimp [t] at hv
    omega
  have notcycle (j : Fin 10) (heq : c (op309_k5_chord_edge (op309_k5_chord_word j)) =
      c (op309_k5_chord_edge (op309_k5_chord_word (j+1)))) :
      ¬ simple_graph_edge_is_rich op309_k5_chord_cycle_graph c (op309_k5_cycle_edge j) := by
    intro hrich
    obtain ⟨h₁,h₂,hne⟩ := op309_k5_cycle_chord_adj j
    exact (hrich _ _ h₁ h₂ hne) heq
  have notchord (a : Fin 5) : ¬ simple_graph_edge_is_rich op309_k5_chord_cycle_graph c (op309_k5_chord_edge a) := by
    intro hrich
    let q (k : Fin 4) : Fin 3 := ⟨(c (op309_k5_cycle_edge (op309_k5_chord_neighbors a k))).val, hcycle _⟩
    have hq : Function.Injective q := by
      intro k l heq
      by_contra hne
      have hedge : op309_k5_cycle_edge (op309_k5_chord_neighbors a k) ≠
          op309_k5_cycle_edge (op309_k5_chord_neighbors a l) := by
        intro hh
        exact hne (op309_k5_chord_neighbor_injective a hh)
      have hval : c (op309_k5_cycle_edge (op309_k5_chord_neighbors a k)) =
          c (op309_k5_cycle_edge (op309_k5_chord_neighbors a l)) := by
        apply Fin.ext
        have hv := congrArg Fin.val heq
        simpa only [q] using hv
      exact (hrich _ _ (op309_k5_chord_neighbor_adj a k) (op309_k5_chord_neighbor_adj a l) hedge) hval
    have hcard := Fintype.card_le_of_injective q hq
    norm_num at hcard
  have hnear : op309_k5_chord_cycle_graph.lineGraph.Adj (op309_k5_cycle_edge (i+1)) (op309_k5_cycle_edge i) :=
    (op309_k5_cycle_neighbor_exhaust i _).2 (Or.inl rfl)
  obtain ⟨f, hf, hfrich⟩ := hrn (op309_k5_cycle_edge (i+1)) ⟨_, hnear⟩
  rcases (op309_k5_cycle_neighbor_exhaust i f).1 hf with h | h | h | h
  · subst f
    exact notcycle i (same hleft) hfrich
  · subst f
    have hright' : t (op309_k5_chord_word (i+2)) = t (op309_k5_chord_word ((i+2)+1)) := by
      simpa only [add_assoc, show (2 : Fin 10) + 1 = 3 by decide] using hright
    exact notcycle (i+2) (same hright') hfrich
  · subst f
    exact notchord _ hfrich
  · subst f
    exact notchord _ hfrich
