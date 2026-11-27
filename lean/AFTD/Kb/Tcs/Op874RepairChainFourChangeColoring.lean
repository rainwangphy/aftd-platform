import AFTD.Prelude
import AFTD.Kb.Tcs.Op874RepairChainEnds
import AFTD.Kb.Tcs.Op874RepairBaseColor
import AFTD.Kb.Tcs.TruncationLocalStatesStrongColoringIff
import AFTD.Kb.Tcs.Op874RepairBaseRight
import AFTD.Kb.Tcs.Op874RepairBaseLeft
import AFTD.Kb.Tcs.TruncationExposedPair
import AFTD.Kb.Tcs.TruncationLocalStatesDefineStrongColoring
import AFTD.Kb.GameTheoryEconomics.Deviate
import AFTD.Kb.Tcs.G

/-!
# op874_repair_chain_four_change_coloring

Topic: graphs   Node: 49d69458796e

Provenance: helper lemma. Saturated fixed-color repair obstruction for OP-874, https://arxiv.org/abs/2610.41950, Section 2.

For every positive block count there is a compatible strong local two-versus-four coloring of the chain that changes exactly four factor colors per block from the reference.
-/

open scoped Sym2

/-- The external colours of the four-change colouring: the reference palette with the four factor
edges 1, 5, 10, 15 recoloured. -/
def op874_repair_chain_four_change_coloring_F : Fin 30 → Fin 6 :=
  ![4,3,5,2,4,5,2,3,4,3,2,4,2,5,3,5,4,3,2,5,1,0,0,1,0,0,0,1,1,1]

/-- The hidden colours of the four-change colouring, by port and edge index; entries at
non-incident index pairs are irrelevant and set to zero. -/
def op874_repair_chain_four_change_coloring_H : Fin 20 → Fin 30 → Fin 6 := ![
  ![2,0,0,0,0,0,0,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  ![5,2,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0,0,0,0],
  ![0,1,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0],
  ![0,0,4,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  ![0,0,0,0,3,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,0,0,0,0,0,0,0,0,0],
  ![0,0,0,0,3,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0],
  ![0,0,0,0,0,3,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0,0],
  ![0,0,0,0,0,0,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0,0,0,0],
  ![0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,3,0,0,1,0,0,0,0,0,0,0],
  ![0,0,0,0,0,0,0,0,1,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0],
  ![0,0,0,0,0,0,0,0,0,1,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,0,0,0],
  ![0,0,0,0,0,0,0,0,0,0,1,5,0,0,0,0,0,0,0,0,0,0,0,0,3,0,0,0,0,0],
  ![0,0,0,0,0,0,0,0,0,0,0,3,5,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  ![0,0,0,0,0,0,0,0,0,0,0,0,3,4,0,0,0,0,0,0,0,0,0,0,0,1,0,0,0,0],
  ![0,0,0,0,0,0,0,0,0,0,0,0,0,2,4,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0],
  ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,4,0,0,0,0,0,0,0,0,0,0,1,0,0,0],
  ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,0,0,0,3],
  ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,2,0,0,0,0,0,0,0,0,0,0,5,0,0],
  ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,5,0,0,0,0,0,0,0,0,0,0,4,0],
  ![0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,4,3,0,0,0,0,0,0,0,0,0,0]]

/-- The two ports of each block edge index: the entries of the 29 block edges, and 16/19 for the
matching-port index 29. -/
def op874_repair_chain_four_change_coloring_port : Fin 30 → Fin 20 × Fin 20 :=
  fun i => if i.val < 29 then (op874_repair_base_left i, op874_repair_base_right i) else (16, 19)

/-- The three edge indices incident with a port of the block. -/
def op874_repair_chain_four_change_coloring_inc (p : Fin 20) : Finset (Fin 30) :=
  Finset.univ.filter
    (fun i => (op874_repair_chain_four_change_coloring_port i).1 = p ∨
      (op874_repair_chain_four_change_coloring_port i).2 = p)

/-- The chain edge with index `i` at the vertex `v` (unique when it exists). -/
def op874_repair_chain_four_change_coloring_edge {k : ℕ} [NeZero k]
    (v : Fin k × Fin 20) (i : Fin 30) : Fin k × Fin 30 :=
  (if i.val < 29 then v.1 else if v.2 = 16 then v.1 else v.1 - 1, i)

/-- No block edge is a loop. -/
lemma op874_repair_chain_four_change_coloring_left_ne :
    ∀ i : Fin 30, i.val < 29 → op874_repair_base_left i ≠ op874_repair_base_right i := by
  decide

/-- Membership in the chain edges, in block-local form. -/
lemma op874_repair_chain_four_change_coloring_mem_ends (k : ℕ) [NeZero k]
    (v : Fin k × Fin 20) (e : Fin k × Fin 30) :
    v ∈ op874_repair_chain_ends k e ↔
      (e.2.val < 29 ∧ (v = (e.1, op874_repair_base_left e.2) ∨
        v = (e.1, op874_repair_base_right e.2))) ∨
      (e.2.val = 29 ∧ (v = (e.1, 16) ∨ v = (e.1 + 1, 19))) := by
  obtain ⟨e1, e2⟩ := e
  simp only
  unfold op874_repair_chain_ends
  split_ifs with h
  · subst h; simp
  · have hne : (e2 : Fin 30).val ≠ 29 := fun hh => h (Fin.ext hh)
    have hlt : (e2 : Fin 30).val < 29 := by have := e2.isLt; omega
    simp [hne, hlt]

/-- The port of an incident edge. -/
lemma op874_repair_chain_four_change_coloring_mem_port {k : ℕ} [NeZero k]
    (v : Fin k × Fin 20) (e : Fin k × Fin 30)
    (h : v ∈ op874_repair_chain_ends k e) :
    v.2 = (op874_repair_chain_four_change_coloring_port e.2).1 ∨
      v.2 = (op874_repair_chain_four_change_coloring_port e.2).2 := by
  rw [op874_repair_chain_four_change_coloring_mem_ends] at h
  rcases h with ⟨hi, hv⟩ | ⟨hi, hv⟩
  · have hEP : op874_repair_chain_four_change_coloring_port e.2 =
        (op874_repair_base_left e.2, op874_repair_base_right e.2) := by
      simp [op874_repair_chain_four_change_coloring_port, hi]
    rcases hv with hv | hv
    · left; rw [hEP]; exact (Prod.ext_iff.1 hv).2
    · right; rw [hEP]; exact (Prod.ext_iff.1 hv).2
  · have hEP : op874_repair_chain_four_change_coloring_port e.2 = (16, 19) := by
      simp [op874_repair_chain_four_change_coloring_port, hi]
    rcases hv with hv | hv
    · left; rw [hEP]; exact (Prod.ext_iff.1 hv).2
    · right; rw [hEP]; exact (Prod.ext_iff.1 hv).2

/-- The index of an incident edge lies in the incidence set of the port. -/
lemma op874_repair_chain_four_change_coloring_inc_mem {k : ℕ} [NeZero k]
    (v : Fin k × Fin 20) (e : Fin k × Fin 30)
    (h : v ∈ op874_repair_chain_ends k e) :
    e.2 ∈ op874_repair_chain_four_change_coloring_inc v.2 := by
  have h' := op874_repair_chain_four_change_coloring_mem_port v e h
  rw [op874_repair_chain_four_change_coloring_inc, Finset.mem_filter]
  refine ⟨Finset.mem_univ _, ?_⟩
  rcases h' with h' | h'
  · left; exact h'.symm
  · right; exact h'.symm

/-- Block-local form of the edge indexed by (b, i). -/
lemma op874_repair_chain_four_change_coloring_ends_eq (k : ℕ) [NeZero k]
    (b : Fin k) (i : Fin 30) :
    op874_repair_chain_ends k (b, i) =
      (if i.val < 29 then s((b, op874_repair_base_left i), (b, op874_repair_base_right i))
        else s((b, 16), (b + 1, 19))) := by
  unfold op874_repair_chain_ends
  by_cases h : i.val < 29
  · have hne : (i : Fin 30) ≠ 29 := by intro hh; rw [hh] at h; omega
    rw [if_pos h, if_neg hne]
  · have hge : (i : Fin 30) = 29 := by
      have h1 : i.val ≤ 29 := by have := i.isLt; omega
      have h2 : 29 ≤ i.val := Nat.le_of_not_lt h
      exact Fin.ext (by omega)
    rw [if_neg h, if_pos hge]

/-- The ports of the two endpoints of an edge, up to order. -/
lemma op874_repair_chain_four_change_coloring_ports {k : ℕ} [NeZero k]
    (b : Fin k) (i : Fin 30) (u v : Fin k × Fin 20)
    (h : op874_repair_chain_ends k (b, i) = s(u, v)) :
    (u.2 = (op874_repair_chain_four_change_coloring_port i).1 ∧
        v.2 = (op874_repair_chain_four_change_coloring_port i).2) ∨
      (u.2 = (op874_repair_chain_four_change_coloring_port i).2 ∧
        v.2 = (op874_repair_chain_four_change_coloring_port i).1) := by
  rw [op874_repair_chain_four_change_coloring_ends_eq] at h
  by_cases hi : i.val < 29
  · rw [if_pos hi] at h
    have hP : op874_repair_chain_four_change_coloring_port i =
        (op874_repair_base_left i, op874_repair_base_right i) := by
      simp [op874_repair_chain_four_change_coloring_port, hi]
    rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨by rw [hP, ← h1], by rw [hP, ← h2]⟩
    · exact Or.inr ⟨by rw [hP, ← h2], by rw [hP, ← h1]⟩
  · rw [if_neg hi] at h
    have hP : op874_repair_chain_four_change_coloring_port i = (16, 19) := by
      simp [op874_repair_chain_four_change_coloring_port, hi]
    rcases Sym2.eq_iff.1 h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact Or.inl ⟨by rw [hP, ← h1], by rw [hP, ← h2]⟩
    · exact Or.inr ⟨by rw [hP, ← h2], by rw [hP, ← h1]⟩

/-- An incident edge is determined by its index. -/
lemma op874_repair_chain_four_change_coloring_eq_edge {k : ℕ} [NeZero k]
    (v : Fin k × Fin 20) (e : Fin k × Fin 30)
    (h : v ∈ op874_repair_chain_ends k e) :
    e = op874_repair_chain_four_change_coloring_edge v e.2 := by
  obtain ⟨b, i⟩ := e
  rw [op874_repair_chain_four_change_coloring_mem_ends] at h
  rcases h with ⟨hi, hv⟩ | ⟨hi29, hv⟩
  · have hE : op874_repair_chain_four_change_coloring_edge v i = (v.1, i) := by
      simp [op874_repair_chain_four_change_coloring_edge, hi]
    rw [hE]
    rcases hv with hv | hv
    · rw [hv]
    · rw [hv]
  · have hge : ¬ i.val < 29 := by rw [hi29]; omega
    rcases hv with hv | hv
    · have hv2 : v.2 = 16 := (Prod.ext_iff.1 hv).2
      have hE : op874_repair_chain_four_change_coloring_edge v i = (v.1, i) := by
        simp [op874_repair_chain_four_change_coloring_edge, hge, hv2]
      rw [hE, hv]
    · have hv2 : v.2 = 19 := (Prod.ext_iff.1 hv).2
      have hv1 : v.1 = b + 1 := (Prod.ext_iff.1 hv).1
      have hE : op874_repair_chain_four_change_coloring_edge v i = (v.1 - 1, i) := by
        simp [op874_repair_chain_four_change_coloring_edge, hge, hv2]
      rw [hE, hv1]
      simp

/-- Every index incident with the port of `v` gives a genuine edge at `v`. -/
lemma op874_repair_chain_four_change_coloring_edge_mem {k : ℕ} [NeZero k]
    (v : Fin k × Fin 20) (i : Fin 30)
    (hi : i ∈ op874_repair_chain_four_change_coloring_inc v.2) :
    v ∈ op874_repair_chain_ends k (op874_repair_chain_four_change_coloring_edge v i) := by
  have hi' : (op874_repair_chain_four_change_coloring_port i).1 = v.2 ∨
      (op874_repair_chain_four_change_coloring_port i).2 = v.2 := by
    simpa [op874_repair_chain_four_change_coloring_inc] using hi
  by_cases hlt : i.val < 29
  · have hEP : op874_repair_chain_four_change_coloring_port i =
        (op874_repair_base_left i, op874_repair_base_right i) := by
      simp [op874_repair_chain_four_change_coloring_port, hlt]
    have hE : op874_repair_chain_four_change_coloring_edge v i = (v.1, i) := by
      simp [op874_repair_chain_four_change_coloring_edge, hlt]
    rw [hE, op874_repair_chain_four_change_coloring_mem_ends]
    refine Or.inl ⟨hlt, ?_⟩
    rcases hi' with h | h
    · left; rw [hEP] at h; exact Prod.ext rfl h.symm
    · right; rw [hEP] at h; exact Prod.ext rfl h.symm
  · have hge : i.val = 29 := by
      have h1 : i.val ≤ 29 := by have := i.isLt; omega
      have h2 : 29 ≤ i.val := Nat.le_of_not_lt hlt
      omega
    have hEP : op874_repair_chain_four_change_coloring_port i = (16, 19) := by
      simp [op874_repair_chain_four_change_coloring_port, hlt]
    rw [hEP] at hi'
    rcases hi' with h | h
    · have hv : v.2 = 16 := h.symm
      have hE : op874_repair_chain_four_change_coloring_edge v i = (v.1, i) := by
        simp [op874_repair_chain_four_change_coloring_edge, hlt, hv]
      rw [hE, op874_repair_chain_four_change_coloring_mem_ends]
      exact Or.inr ⟨hge, Or.inl (Prod.ext rfl hv)⟩
    · have hv : v.2 = 19 := h.symm
      have hE : op874_repair_chain_four_change_coloring_edge v i = (v.1 - 1, i) := by
        simp [op874_repair_chain_four_change_coloring_edge, hlt, hv]
      rw [hE, op874_repair_chain_four_change_coloring_mem_ends]
      exact Or.inr ⟨hge, Or.inr (Prod.ext (sub_add_cancel v.1 1).symm hv)⟩

/-- Two incident edges with the same index have the same block. -/
lemma op874_repair_chain_four_change_coloring_block_eq {k : ℕ} [NeZero k]
    (v : Fin k × Fin 20) (i : Fin 30) (b b' : Fin k)
    (h : v ∈ op874_repair_chain_ends k (b, i))
    (h' : v ∈ op874_repair_chain_ends k (b', i)) : b = b' := by
  have e1 := op874_repair_chain_four_change_coloring_eq_edge v (b, i) h
  have e2 := op874_repair_chain_four_change_coloring_eq_edge v (b', i) h'
  have : (b, i) = (b', i) := e1.trans e2.symm
  exact (Prod.ext_iff.1 this).1

/-- Every port is incident with exactly three edge indices. -/
lemma op874_repair_chain_four_change_coloring_inc_card :
    ∀ p : Fin 20, (op874_repair_chain_four_change_coloring_inc p).card = 3 := by decide

/-- The external colours are injective on the edges at a port. -/
lemma op874_repair_chain_four_change_coloring_F_inj :
    ∀ p : Fin 20, ∀ a b : Fin 30, a ∈ op874_repair_chain_four_change_coloring_inc p →
      b ∈ op874_repair_chain_four_change_coloring_inc p →
      op874_repair_chain_four_change_coloring_F a = op874_repair_chain_four_change_coloring_F b →
      a = b := by decide

/-- The hidden colours are injective on the edges at a port. -/
lemma op874_repair_chain_four_change_coloring_H_inj :
    ∀ p : Fin 20, ∀ a b : Fin 30, a ∈ op874_repair_chain_four_change_coloring_inc p →
      b ∈ op874_repair_chain_four_change_coloring_inc p →
      op874_repair_chain_four_change_coloring_H p a =
        op874_repair_chain_four_change_coloring_H p b → a = b := by decide

/-- Hidden and external colours are distinct at a common port. -/
lemma op874_repair_chain_four_change_coloring_H_ne_F :
    ∀ p : Fin 20, ∀ a b : Fin 30, a ∈ op874_repair_chain_four_change_coloring_inc p →
      b ∈ op874_repair_chain_four_change_coloring_inc p →
      op874_repair_chain_four_change_coloring_H p a ≠
        op874_repair_chain_four_change_coloring_F b := by decide

/-- The exposed pairs at the two ends of every edge are disjoint. -/
lemma op874_repair_chain_four_change_coloring_disj : ∀ i : Fin 30,
    Disjoint
      ((Finset.univ \
          (op874_repair_chain_four_change_coloring_inc
            (op874_repair_chain_four_change_coloring_port i).1).image
          op874_repair_chain_four_change_coloring_F) \
        {op874_repair_chain_four_change_coloring_H
          (op874_repair_chain_four_change_coloring_port i).1 i})
      ((Finset.univ \
          (op874_repair_chain_four_change_coloring_inc
            (op874_repair_chain_four_change_coloring_port i).2).image
          op874_repair_chain_four_change_coloring_F) \
        {op874_repair_chain_four_change_coloring_H
          (op874_repair_chain_four_change_coloring_port i).2 i}) := by decide

/-- The matching edges keep their reference colours. -/
lemma op874_repair_chain_four_change_coloring_match :
    ∀ j : Fin 30, 20 ≤ j.val →
      op874_repair_chain_four_change_coloring_F j = op874_repair_base_color j := by decide

/-- All factor colours avoid 0 and 1. -/
lemma op874_repair_chain_four_change_coloring_factor :
    ∀ j : Fin 30, j.val < 20 → 2 ≤ (op874_repair_chain_four_change_coloring_F j).val := by decide

/-- Exactly four factor colours deviate from the reference. -/
lemma op874_repair_chain_four_change_coloring_filt_card :
    ((Finset.univ : Finset (Fin 30)).filter
      (fun j => j.val < 20 ∧ op874_repair_chain_four_change_coloring_F j ≠
        op874_repair_base_color j)).card = 4 := by decide

/-- No chain edge is a loop. -/
lemma op874_repair_chain_four_change_coloring_loop (k : ℕ) [NeZero k]
    (e : Fin k × Fin 30) : ¬ (op874_repair_chain_ends k e).IsDiag := by
  obtain ⟨b, i⟩ := e
  rw [op874_repair_chain_four_change_coloring_ends_eq]
  split_ifs with h
  · rw [Sym2.mk_isDiag_iff]
    intro hh
    exact op874_repair_chain_four_change_coloring_left_ne i h (congrArg Prod.snd hh)
  · rw [Sym2.mk_isDiag_iff]
    intro hh
    exact absurd (congrArg Prod.snd hh) (by simp)

/-- The exposed pair equals the explicit finset of unused colours other than the hidden one. -/
lemma op874_repair_chain_four_change_coloring_exposed {k : ℕ} [NeZero k]
    (v : Fin k × Fin 20) (f : Fin k × Fin 30) :
    truncation_exposed_pair (op874_repair_chain_ends k)
      (fun _ e => op874_repair_chain_four_change_coloring_F e.2)
      (fun v e => op874_repair_chain_four_change_coloring_H v.2 e.2) v f =
      ↑((Finset.univ \
            (op874_repair_chain_four_change_coloring_inc v.2).image
              op874_repair_chain_four_change_coloring_F) \
          {op874_repair_chain_four_change_coloring_H v.2 f.2}) := by
  ext w
  simp only [truncation_exposed_pair, Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_sdiff,
    Finset.mem_univ, true_and, Finset.mem_image, Finset.mem_singleton]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨fun ⟨j, hj, hw⟩ =>
      h1 (op874_repair_chain_four_change_coloring_edge v j)
        (op874_repair_chain_four_change_coloring_edge_mem v j hj) hw, h2⟩
  · rintro ⟨h1, h2⟩
    refine ⟨?_, h2⟩
    intro g hg hcon
    exact h1 ⟨g.2, op874_repair_chain_four_change_coloring_inc_mem v g hg, hcon⟩

/-- The chain is cubic at every vertex. -/
lemma op874_repair_chain_four_change_coloring_cubic (k : ℕ) [NeZero k]
    (v : Fin k × Fin 20) :
    Set.ncard {e | v ∈ op874_repair_chain_ends k e} = 3 := by
  have hset : {e | v ∈ op874_repair_chain_ends k e} =
      ↑((op874_repair_chain_four_change_coloring_inc v.2).image
        (op874_repair_chain_four_change_coloring_edge v)) := by
    ext e
    simp only [Set.mem_ofPred_eq, Finset.mem_coe, Finset.mem_image]
    exact ⟨fun h => ⟨e.2, op874_repair_chain_four_change_coloring_inc_mem v e h,
        (op874_repair_chain_four_change_coloring_eq_edge v e h).symm⟩,
      fun ⟨j, hj, hje⟩ => hje ▸ op874_repair_chain_four_change_coloring_edge_mem v j hj⟩
  rw [hset, Set.ncard_coe_finset]
  rw [Finset.card_image_of_injOn (f := op874_repair_chain_four_change_coloring_edge v)
    (s := op874_repair_chain_four_change_coloring_inc v.2)]
  · exact op874_repair_chain_four_change_coloring_inc_card v.2
  · intro a _ b _ hab
    exact congrArg Prod.snd hab

theorem op874_repair_chain_four_change_coloring (k : ℕ) [NeZero k] :
    ∃ (c : Fin k × Fin 30 → Fin 6)
      (h : Fin k × Fin 20 → Fin k × Fin 30 → Fin 6),
      (∀ v e f, v ∈ op874_repair_chain_ends k e → v ∈ op874_repair_chain_ends k f → c e = c f → e = f) ∧
      (∀ v e f, v ∈ op874_repair_chain_ends k e → v ∈ op874_repair_chain_ends k f → h v e = h v f → e = f) ∧
      (∀ v e f, v ∈ op874_repair_chain_ends k e → v ∈ op874_repair_chain_ends k f → h v e ≠ c f) ∧
      truncation_local_states_define_strong_coloring
        (op874_repair_chain_ends k) (fun _ e => c e) h ∧
      (∀ i j, 20 ≤ (j : Fin 30).val → c (i,j) = op874_repair_base_color j) ∧
      (∀ i j, (j : Fin 30).val < 20 → 2 ≤ (c (i,j)).val) ∧
      (Finset.univ.filter (fun e : Fin k × Fin 30 =>
        e.2.val < 20 ∧ c e ≠ op874_repair_base_color e.2)).card = 4 * k := by
  classical
  refine ⟨fun e => op874_repair_chain_four_change_coloring_F e.2,
          fun v e => op874_repair_chain_four_change_coloring_H v.2 e.2, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rintro v ⟨be, ie⟩ ⟨bf, jf⟩ he hf hceq
    have h1 : ie = jf :=
      op874_repair_chain_four_change_coloring_F_inj v.2 ie jf
        (op874_repair_chain_four_change_coloring_inc_mem v (be, ie) he)
        (op874_repair_chain_four_change_coloring_inc_mem v (bf, jf) hf) hceq
    have h2 : be = bf :=
      op874_repair_chain_four_change_coloring_block_eq v jf be bf (h1 ▸ he) hf
    exact Prod.ext h2 h1
  · rintro v ⟨be, ie⟩ ⟨bf, jf⟩ he hf hheq
    have h1 : ie = jf :=
      op874_repair_chain_four_change_coloring_H_inj v.2 ie jf
        (op874_repair_chain_four_change_coloring_inc_mem v (be, ie) he)
        (op874_repair_chain_four_change_coloring_inc_mem v (bf, jf) hf) hheq
    have h2 : be = bf :=
      op874_repair_chain_four_change_coloring_block_eq v jf be bf (h1 ▸ he) hf
    exact Prod.ext h2 h1
  · rintro v ⟨be, ie⟩ ⟨bf, jf⟩ he hf
    exact op874_repair_chain_four_change_coloring_H_ne_F v.2 ie jf
      (op874_repair_chain_four_change_coloring_inc_mem v (be, ie) he)
      (op874_repair_chain_four_change_coloring_inc_mem v (bf, jf) hf)
  · refine (truncation_local_states_strong_coloring_iff (Ω := Fin 6) (by decide)
      (op874_repair_chain_ends k) (op874_repair_chain_four_change_coloring_loop k)
      (op874_repair_chain_four_change_coloring_cubic k)
      (fun _ e => op874_repair_chain_four_change_coloring_F e.2)
      (fun v e => op874_repair_chain_four_change_coloring_H v.2 e.2)
      ?_ ?_ ?_).2 ?_
    · rintro v ⟨be, ie⟩ ⟨bf, jf⟩ he hf hceq
      have h1 : ie = jf :=
        op874_repair_chain_four_change_coloring_F_inj v.2 ie jf
          (op874_repair_chain_four_change_coloring_inc_mem v (be, ie) he)
          (op874_repair_chain_four_change_coloring_inc_mem v (bf, jf) hf) hceq
      have h2 : be = bf :=
        op874_repair_chain_four_change_coloring_block_eq v jf be bf (h1 ▸ he) hf
      exact Prod.ext h2 h1
    · rintro v ⟨be, ie⟩ ⟨bf, jf⟩ he hf hheq
      have h1 : ie = jf :=
        op874_repair_chain_four_change_coloring_H_inj v.2 ie jf
          (op874_repair_chain_four_change_coloring_inc_mem v (be, ie) he)
          (op874_repair_chain_four_change_coloring_inc_mem v (bf, jf) hf) hheq
      have h2 : be = bf :=
        op874_repair_chain_four_change_coloring_block_eq v jf be bf (h1 ▸ he) hf
      exact Prod.ext h2 h1
    · rintro v ⟨be, ie⟩ ⟨bf, jf⟩ he hf
      exact op874_repair_chain_four_change_coloring_H_ne_F v.2 ie jf
        (op874_repair_chain_four_change_coloring_inc_mem v (be, ie) he)
        (op874_repair_chain_four_change_coloring_inc_mem v (bf, jf) hf)
    · rintro ⟨b, i⟩ u v hE
      refine ⟨rfl, ?_⟩
      rw [op874_repair_chain_four_change_coloring_exposed u (b, i),
        op874_repair_chain_four_change_coloring_exposed v (b, i), Finset.disjoint_coe]
      rcases op874_repair_chain_four_change_coloring_ports b i u v hE with ⟨hu, hv⟩ | ⟨hu, hv⟩
      · rw [hu, hv]
        exact op874_repair_chain_four_change_coloring_disj i
      · rw [hu, hv]
        exact (op874_repair_chain_four_change_coloring_disj i).symm
  · intro i j hj
    exact op874_repair_chain_four_change_coloring_match j hj
  · intro i j hj
    exact op874_repair_chain_four_change_coloring_factor j hj
  · have hfilter :
        (Finset.univ.filter (fun e : Fin k × Fin 30 =>
            e.2.val < 20 ∧ op874_repair_chain_four_change_coloring_F e.2 ≠
              op874_repair_base_color e.2))
          = (Finset.univ : Finset (Fin k)) ×ˢ
            ((Finset.univ : Finset (Fin 30)).filter
              (fun j => j.val < 20 ∧
                op874_repair_chain_four_change_coloring_F j ≠ op874_repair_base_color j)) := by
      ext e
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product]
    rw [hfilter, Finset.card_product, Finset.card_univ, Fintype.card_fin,
      op874_repair_chain_four_change_coloring_filt_card]
    ring
