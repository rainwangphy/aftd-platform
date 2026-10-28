import AFTD.Prelude
import AFTD.Kb.Tcs.CompleteGraphOddLineGraphChromaticNumberEq
import AFTD.Kb.Tcs.WildNumberCompleteGraph279MinProperColoringEq
import AFTD.Kb.Tcs.WildNumberCompleteGraphMinProperColoringGe

/-!
# wild_complete_thirteen_one_swap_repair_obstruction

Topic: graphs   Node: c2c1b9c93e6f

Provenance: helper lemma. Obstruction to a proposed finite-range repair step for OP-306. Experiment 7988 constructs the symmetric idempotent color table; the Lean proof independently checks its rows, the unique bad cut, all swaps, and the displayed two-swap repair using kernel reduction. This is a failed proof-route certificate; the original conjecture remains open.

There exists a minimum proper 13-coloring of K_13, normalized so that color i misses vertex i, with this property. The fixed partition {0,1,2}, {3,4,5}, {6,7,8}, {9,10,11,12} has exactly one closed color cut among the seven cuts up to complements: its first triple, for color 0. Every single swap of vertices from different blocks leaves a closed color cut. Swapping vertices 0 and 3 and then vertices 0 and 6 produces a partition with no closed color cut. The seven cuts are the four individual blocks and the three unions of two of the triple blocks.
-/

set_option maxHeartbeats 1000000
set_option maxRecDepth 100000

def wsc_repair_table : Fin 13 → Fin 13 → Fin 13 := ![
  ![0, 8, 12, 4, 5, 1, 10, 2, 9, 6, 11, 3, 7],
  ![8, 1, 0, 7, 11, 3, 9, 6, 10, 5, 2, 12, 4],
  ![12, 0, 2, 5, 1, 10, 8, 11, 7, 4, 6, 9, 3],
  ![4, 7, 5, 3, 10, 11, 2, 9, 6, 12, 8, 1, 0],
  ![5, 11, 1, 10, 4, 9, 3, 0, 2, 7, 12, 6, 8],
  ![1, 3, 10, 11, 9, 5, 7, 4, 12, 2, 0, 8, 6],
  ![10, 9, 8, 2, 3, 7, 6, 12, 11, 1, 4, 0, 5],
  ![2, 6, 11, 9, 0, 4, 12, 7, 3, 8, 1, 5, 10],
  ![9, 10, 7, 6, 2, 12, 11, 3, 8, 0, 5, 4, 1],
  ![6, 5, 4, 12, 7, 2, 1, 8, 0, 9, 3, 10, 11],
  ![11, 2, 6, 8, 12, 0, 4, 1, 5, 3, 10, 7, 9],
  ![3, 12, 9, 1, 6, 8, 0, 5, 4, 10, 7, 11, 2],
  ![7, 4, 3, 0, 8, 6, 5, 10, 1, 11, 9, 2, 12]
]

def wsc_repair_blocks : Fin 4 → Finset (Fin 13) := ![{0,1,2},{3,4,5},{6,7,8},{9,10,11,12}]

def wsc_repair_cuts (B : Fin 4 → Finset (Fin 13)) : Fin 7 → Finset (Fin 13) :=
  ![B 0, B 1, B 2, B 3, B 0 ∪ B 1, B 0 ∪ B 2, B 1 ∪ B 2]

def wsc_repair_owner (v : Fin 13) : Fin 4 := ⟨min (v.val/3) 3, by omega⟩

def wsc_repair_swap (B : Fin 4 → Finset (Fin 13)) (u v : Fin 13) : Fin 4 → Finset (Fin 13) :=
  fun t => (B t).image (Equiv.swap u v)

def wsc_repair_closed (i : Fin 13) (U : Finset (Fin 13)) : Prop :=
  ∀ v ∈ U, ∀ w : Fin 13, wsc_repair_table v w = i → w ∈ U

instance wsc_repair_closed_decidable (i : Fin 13) (U : Finset (Fin 13)) :
    Decidable (wsc_repair_closed i U) := by unfold wsc_repair_closed; infer_instance

lemma wsc_repair_table_valid :
    (∀ v : Fin 13, wsc_repair_table v v = v) ∧
    (∀ u v : Fin 13, wsc_repair_table u v = wsc_repair_table v u) ∧
    (∀ v u w : Fin 13, wsc_repair_table v u = wsc_repair_table v w → u = w) := by
  decide +kernel

lemma wsc_repair_table_missing :
    ∀ i v : Fin 13, (∀ w : Fin 13, v ≠ w → wsc_repair_table v w ≠ i) ↔ v = i := by
  decide +kernel

lemma wsc_repair_unique_bad_cut :
    ∀ (j : Fin 7) (i : Fin 13), wsc_repair_closed i (wsc_repair_cuts wsc_repair_blocks j) ↔ j = 0 ∧ i = 0 := by
  decide +kernel

lemma wsc_repair_all_swaps_bad :
    ∀ u v : Fin 13, wsc_repair_owner u ≠ wsc_repair_owner v →
      ∃ (j : Fin 7) (i : Fin 13),
        wsc_repair_closed i (wsc_repair_cuts (wsc_repair_swap wsc_repair_blocks u v) j) := by
  decide +kernel

lemma wsc_repair_two_swaps_good :
    ∀ (j : Fin 7) (i : Fin 13), ¬wsc_repair_closed i
      (wsc_repair_cuts (wsc_repair_swap (wsc_repair_swap wsc_repair_blocks 0 3) 0 6) j) := by
  decide +kernel

noncomputable def wsc_repair_coloring :
    (⊤ : SimpleGraph (Fin 13)).lineGraph.Coloring (Fin 13) := by
  let col : Sym2 (Fin 13) → Fin 13 := Sym2.lift ⟨wsc_repair_table, wsc_repair_table_valid.2.1⟩
  refine SimpleGraph.Coloring.mk (fun e => col e.val) ?_
  intro e₁ e₂ h hc
  rw [SimpleGraph.lineGraph_adj_iff_exists] at h
  obtain ⟨hne, v, h1, h2⟩ := h
  obtain ⟨a, ha⟩ := Sym2.mem_iff_exists.mp h1
  obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.mp h2
  have ht : wsc_repair_table v a = wsc_repair_table v b := by
    simpa only [col, ha, hb, Sym2.lift_mk] using hc
  have hab := wsc_repair_table_valid.2.2 v a b ht
  apply hne
  apply Subtype.ext
  rw [ha,hb,hab]

lemma wsc_repair_coloring_pair (u v : Fin 13) (h : u ≠ v) :
    wsc_repair_coloring ⟨s(u,v), wild_kn_mem h⟩ = wsc_repair_table u v := rfl

lemma wsc_repair_closed_iff (i : Fin 13) (U : Finset (Fin 13)) :
    w279_closed wsc_repair_coloring i U ↔ wsc_repair_closed i U := by
  constructor
  · intro h v hv w hc
    by_cases he : v = w
    · simpa only [← he] using hv
    · exact h v hv w he ((wsc_repair_coloring_pair v w he).trans hc)
  · intro h v hv w hvw hc
    exact h v hv w ((wsc_repair_coloring_pair v w hvw).symm.trans hc)

theorem wild_complete_thirteen_one_swap_repair_obstruction :
    (⊤ : SimpleGraph (Fin 13)).lineGraph.chromaticNumber = 13 ∧
    ∃ c : (⊤ : SimpleGraph (Fin 13)).lineGraph.Coloring (Fin 13),
      (∀ i v : Fin 13, (∀ w (hvw : v ≠ w), c ⟨s(v,w), wild_kn_mem hvw⟩ ≠ i) ↔ v = i) ∧
      (∀ (j : Fin 7) (i : Fin 13), w279_closed c i (wsc_repair_cuts wsc_repair_blocks j) ↔ j = 0 ∧ i = 0) ∧
      (∀ u v : Fin 13, wsc_repair_owner u ≠ wsc_repair_owner v →
        ∃ (j : Fin 7) (i : Fin 13), w279_closed c i
          (wsc_repair_cuts (wsc_repair_swap wsc_repair_blocks u v) j)) ∧
      (∀ (j : Fin 7) (i : Fin 13), ¬w279_closed c i
        (wsc_repair_cuts (wsc_repair_swap (wsc_repair_swap wsc_repair_blocks 0 3) 0 6) j)) := by
  refine ⟨complete_graph_odd_line_graph_chromatic_number_eq 13 (by norm_num) (by decide), wsc_repair_coloring, ?_, ?_, ?_, ?_⟩
  · intro i v
    rw [← wsc_repair_table_missing i v]
    constructor
    · intro h w hvw
      rw [← wsc_repair_coloring_pair v w hvw]
      exact h w hvw
    · intro h w hvw
      rw [wsc_repair_coloring_pair v w hvw]
      exact h w hvw
  · intro j i
    rw [wsc_repair_closed_iff]
    exact wsc_repair_unique_bad_cut j i
  · intro u v huv
    obtain ⟨j,i,hi⟩ := wsc_repair_all_swaps_bad u v huv
    exact ⟨j,i,(wsc_repair_closed_iff i _).2 hi⟩
  · intro j i
    rw [wsc_repair_closed_iff]
    exact wsc_repair_two_swaps_good j i
