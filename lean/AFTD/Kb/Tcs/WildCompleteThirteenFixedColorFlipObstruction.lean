import AFTD.Prelude
import AFTD.Kb.Tcs.WildCompleteThirteenOneSwapRepairObstruction
import AFTD.Kb.Tcs.WildNumberCompleteGraphMinProperColoringGe
import AFTD.Kb.Tcs.WildNumberCompleteGraph279MinProperColoringEq
import AFTD.Kb.Tcs.CompleteGraphOddLineGraphChromaticNumberEq

/-!
# wild_complete_thirteen_fixed_color_flip_obstruction

Topic: graphs   Node: 8bfb59e0dbe3

Provenance: helper lemma. Failed structural exchange-route certificate for the OP-306 campaign, related to arXiv:2610.22142, Section 3.3.2. Experiment 8169 found the table; kernel finite checks certify the matrix, all 64 flip masks, and the unrestricted repair. A permutation-completeness proof reduces arbitrarily long flip words to those masks. This refutes the fixed-color endpoint-flip completion strategy, not the wild-number conjecture.

There is a normalized minimum proper 13-coloring of K_13 for which the partition {0,1,2},{3,4,5},{6,7,8},{9,10,11,12} has exactly one closed cut-color pair, the first triple for color 0. After swapping 1 and 3 it has exactly one defect, the second triple for color 1. Every finite sequence of flips of endpoints within the six color-0 matching edges keeps all color-0 cuts open but leaves some color cut closed. An unrestricted swap of 0 and 1 after the first swap makes all seven cuts open. The color-0 matching is {1,2},{3,6},{4,9},{5,10},{7,11},{8,12}.
-/

open scoped Classical
set_option maxHeartbeats 2000000
set_option maxRecDepth 100000

def wfo_table : Fin 13 → Fin 13 → Fin 13 := ![
  ![0, 10, 11, 5, 12, 6, 9, 3, 2, 7, 8, 1, 4],
  ![10, 1, 0, 7, 2, 9, 12, 6, 5, 3, 11, 4, 8],
  ![11, 0, 2, 9, 10, 4, 1, 12, 3, 8, 6, 7, 5],
  ![5, 7, 9, 3, 8, 12, 0, 2, 10, 1, 4, 6, 11],
  ![12, 2, 10, 8, 4, 1, 7, 11, 6, 0, 3, 5, 9],
  ![6, 9, 4, 12, 1, 5, 10, 8, 11, 2, 0, 3, 7],
  ![9, 12, 1, 0, 7, 10, 6, 5, 4, 11, 2, 8, 3],
  ![3, 6, 12, 2, 11, 8, 5, 7, 1, 4, 9, 0, 10],
  ![2, 5, 3, 10, 6, 11, 4, 1, 8, 12, 7, 9, 0],
  ![7, 3, 8, 1, 0, 2, 11, 4, 12, 9, 5, 10, 6],
  ![8, 11, 6, 4, 3, 0, 2, 9, 7, 5, 10, 12, 1],
  ![1, 4, 7, 6, 5, 3, 8, 0, 9, 10, 12, 11, 2],
  ![4, 8, 5, 11, 9, 7, 3, 10, 0, 6, 1, 2, 12]
]

def wfo_mate : Fin 13 → Fin 13 := ![0,2,1,6,9,10,3,11,12,4,5,7,8]
def wfo_left : Fin 6 → Fin 13 := ![1,3,4,5,7,8]
def wfo_right : Fin 6 → Fin 13 := ![2,6,9,10,11,12]
def wfo_index : Fin 13 → Fin 6 := ![0,0,0,1,2,3,1,4,5,2,3,4,5]
def wfo_flip (bits : Fin 6 → Bool) (v : Fin 13) : Fin 13 :=
  if bits (wfo_index v) then wfo_mate v else v

def wfo_start : Fin 4 → Finset (Fin 13) := wsc_repair_swap wsc_repair_blocks 1 3

def wfo_closed (i : Fin 13) (U : Finset (Fin 13)) : Prop :=
  ∀ v ∈ U, ∀ w : Fin 13, wfo_table v w = i → w ∈ U
instance wfo_closed_decidable (i : Fin 13) (U : Finset (Fin 13)) : Decidable (wfo_closed i U) :=
  by unfold wfo_closed; infer_instance

lemma wfo_valid :
    (∀ v, wfo_table v v = v) ∧
    (∀ u v, wfo_table u v = wfo_table v u) ∧
    (∀ v u w, wfo_table v u = wfo_table v w → u = w) := by decide +kernel

lemma wfo_zero_mate : ∀ u v : Fin 13, wfo_table u v = 0 ↔ v = wfo_mate u := by decide +kernel

lemma wfo_missing :
    ∀ i v : Fin 13, (∀ w : Fin 13, v ≠ w → wfo_table v w ≠ i) ↔ v = i := by decide +kernel

lemma wfo_base : ∀ (j : Fin 7) (i : Fin 13),
    wfo_closed i (wsc_repair_cuts wsc_repair_blocks j) ↔ j = 0 ∧ i = 0 := by decide +kernel

lemma wfo_orbit_bad : ∀ bits : Fin 6 → Bool,
    ∃ (j : Fin 7) (i : Fin 13), wfo_closed i
      (wsc_repair_cuts (fun t => (wfo_start t).image (wfo_flip bits)) j) := by decide +kernel

lemma wfo_orbit_zero_good : ∀ (bits : Fin 6 → Bool) (j : Fin 7),
    ¬wfo_closed 0 (wsc_repair_cuts (fun t => (wfo_start t).image (wfo_flip bits)) j) := by decide +kernel

lemma wfo_free_repair : ∀ (j : Fin 7) (i : Fin 13),
    ¬wfo_closed i (wsc_repair_cuts (wsc_repair_swap wfo_start 0 1) j) := by decide +kernel

lemma wfo_pair_permutation (σ : Equiv.Perm (Fin 13))
    (hσ : ∀ v, σ v = v ∨ σ v = wfo_mate v) :
    ∃ bits : Fin 6 → Bool, ∀ v, σ v = wfo_flip bits v := by
  let bits : Fin 6 → Bool := fun j => decide (σ (wfo_left j) = wfo_right j)
  refine ⟨bits,?_⟩
  have pair (a b : Fin 13) (hab : a ≠ b)
      (ha : σ a = a ∨ σ a = b) (hb : σ b = b ∨ σ b = a) :
      σ a = (if σ a = b then b else a) ∧
        σ b = (if σ a = b then a else b) := by
    by_cases h : σ a = b
    · simp only [if_pos h]
      refine ⟨h,?_⟩
      rcases hb with hb | hb
      · exact False.elim (hab (σ.injective (h.trans hb.symm)))
      · exact hb
    · simp only [if_neg h]
      have ha' : σ a = a := ha.resolve_right h
      refine ⟨ha',?_⟩
      rcases hb with hb | hb
      · exact hb
      · exact False.elim (hab (σ.injective (ha'.trans hb.symm)))
  have hp : ∀ j : Fin 6,
      σ (wfo_left j) = (if bits j then wfo_right j else wfo_left j) ∧
        σ (wfo_right j) = (if bits j then wfo_left j else wfo_right j) := by
    intro j
    have hj1 : wfo_mate (wfo_left j) = wfo_right j := by fin_cases j <;> decide
    have hj2 : wfo_mate (wfo_right j) = wfo_left j := by fin_cases j <;> decide
    have hjne : wfo_left j ≠ wfo_right j := by fin_cases j <;> decide
    have h1 := hσ (wfo_left j)
    have h2 := hσ (wfo_right j)
    rw [hj1] at h1
    rw [hj2] at h2
    simpa only [bits, decide_eq_true_eq] using pair (wfo_left j) (wfo_right j) hjne h1 h2
  intro v
  fin_cases v
  · change σ 0 = (if bits 0 then (0 : Fin 13) else 0)
    split <;> exact (hσ 0).elim id id
  all_goals first
    | exact (hp 0).1 | exact (hp 0).2
    | exact (hp 1).1 | exact (hp 1).2
    | exact (hp 2).1 | exact (hp 2).2
    | exact (hp 3).1 | exact (hp 3).2
    | exact (hp 4).1 | exact (hp 4).2
    | exact (hp 5).1 | exact (hp 5).2


lemma wfo_flip_involutive : ∀ (bits : Fin 6 → Bool) (v : Fin 13),
    wfo_flip bits (wfo_flip bits v) = v := by decide +kernel

lemma wfo_start_one_defect : ∀ (j : Fin 7) (i : Fin 13),
    wfo_closed i (wsc_repair_cuts wfo_start j) ↔ j = 1 ∧ i = 1 := by decide +kernel

def wfo_edge_swap (j : Fin 6) : Equiv.Perm (Fin 13) := Equiv.swap (wfo_left j) (wfo_right j)
def wfo_word (L : List (Fin 6)) : Equiv.Perm (Fin 13) := (L.map wfo_edge_swap).prod

lemma wfo_word_pair (L : List (Fin 6)) : ∀ v, wfo_word L v = v ∨ wfo_word L v = wfo_mate v := by
  have single : ∀ (j : Fin 6) (v : Fin 13), wfo_edge_swap j v = v ∨ wfo_edge_swap j v = wfo_mate v := by
    decide +kernel
  have inv : ∀ v : Fin 13, wfo_mate (wfo_mate v) = v := by decide +kernel
  induction L with
  | nil => intro v; exact Or.inl rfl
  | cons j L ih =>
    intro v
    change wfo_edge_swap j (wfo_word L v) = v ∨ wfo_edge_swap j (wfo_word L v) = wfo_mate v
    rcases ih v with hv | hv
    · rw [hv]; exact single j v
    · rw [hv]
      rcases single j (wfo_mate v) with he | he
      · exact Or.inr he
      · exact Or.inl (he.trans (inv v))

noncomputable def wfo_coloring : (⊤ : SimpleGraph (Fin 13)).lineGraph.Coloring (Fin 13) := by
  let col : Sym2 (Fin 13) → Fin 13 := Sym2.lift ⟨wfo_table,wfo_valid.2.1⟩
  refine SimpleGraph.Coloring.mk (fun e => col e.val) ?_
  intro e₁ e₂ h hc
  rw [SimpleGraph.lineGraph_adj_iff_exists] at h
  obtain ⟨hne,v,h1,h2⟩ := h
  obtain ⟨a,ha⟩ := Sym2.mem_iff_exists.mp h1
  obtain ⟨b,hb⟩ := Sym2.mem_iff_exists.mp h2
  have ht : wfo_table v a = wfo_table v b := by
    simpa only [col,ha,hb,Sym2.lift_mk] using hc
  have hab := wfo_valid.2.2 v a b ht
  apply hne
  apply Subtype.ext
  rw [ha,hb,hab]

lemma wfo_coloring_pair (u v : Fin 13) (h : u ≠ v) :
    wfo_coloring ⟨s(u,v),wild_kn_mem h⟩ = wfo_table u v := rfl

lemma wfo_closed_iff (i : Fin 13) (U : Finset (Fin 13)) :
    w279_closed wfo_coloring i U ↔ wfo_closed i U := by
  constructor
  · intro h v hv w hc
    by_cases he : v = w
    · simpa only [← he] using hv
    · exact h v hv w he ((wfo_coloring_pair v w he).trans hc)
  · intro h v hv w hvw hc
    exact h v hv w ((wfo_coloring_pair v w hvw).symm.trans hc)

theorem wild_complete_thirteen_fixed_color_flip_obstruction :
    (⊤ : SimpleGraph (Fin 13)).lineGraph.chromaticNumber = 13 ∧
    ∃ c : (⊤ : SimpleGraph (Fin 13)).lineGraph.Coloring (Fin 13),
      (∀ i v : Fin 13, (∀ w (hvw : v ≠ w), c ⟨s(v,w),wild_kn_mem hvw⟩ ≠ i) ↔ v = i) ∧
      (∀ (u v : Fin 13) (huv : u ≠ v), c ⟨s(u,v),wild_kn_mem huv⟩ = 0 ↔ v = wfo_mate u) ∧
      (∀ (j : Fin 7) (i : Fin 13), w279_closed c i (wsc_repair_cuts wsc_repair_blocks j) ↔ j = 0 ∧ i = 0) ∧
      (∀ (j : Fin 7) (i : Fin 13), w279_closed c i (wsc_repair_cuts wfo_start j) ↔ j = 1 ∧ i = 1) ∧
      (∀ L : List (Fin 6),
        (∀ j : Fin 7, ¬w279_closed c 0 (wsc_repair_cuts (fun t => (wfo_start t).image (wfo_word L)) j)) ∧
        ∃ (j : Fin 7) (i : Fin 13), w279_closed c i (wsc_repair_cuts (fun t => (wfo_start t).image (wfo_word L)) j)) ∧
      (∀ (j : Fin 7) (i : Fin 13), ¬w279_closed c i (wsc_repair_cuts (wsc_repair_swap wfo_start 0 1) j)) := by
  refine ⟨complete_graph_odd_line_graph_chromatic_number_eq 13 (by norm_num) (by decide),wfo_coloring,?_,?_,?_,?_,?_,?_⟩
  · intro i v
    rw [← wfo_missing i v]
    constructor
    · intro h w hvw
      rw [← wfo_coloring_pair v w hvw]; exact h w hvw
    · intro h w hvw
      rw [wfo_coloring_pair v w hvw]; exact h w hvw
  · intro u v huv
    rw [wfo_coloring_pair u v huv]
    exact wfo_zero_mate u v
  · intro j i
    rw [wfo_closed_iff]; exact wfo_base j i
  · intro j i
    rw [wfo_closed_iff]; exact wfo_start_one_defect j i
  · intro L
    obtain ⟨bits,hbits⟩ := wfo_pair_permutation (wfo_word L) (wfo_word_pair L)
    have he : (fun t => (wfo_start t).image (wfo_word L)) =
        (fun t => (wfo_start t).image (wfo_flip bits)) := by
      funext t
      apply Finset.image_congr
      intro v _
      exact hbits v
    rw [he]
    constructor
    · intro j; rw [wfo_closed_iff]; exact wfo_orbit_zero_good bits j
    · obtain ⟨j,i,hi⟩ := wfo_orbit_bad bits
      exact ⟨j,i,(wfo_closed_iff i _).2 hi⟩
  · intro j i
    rw [wfo_closed_iff]; exact wfo_free_repair j i
