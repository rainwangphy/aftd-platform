import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphDirectedCycleOn

/-!
# digraph_digon_cycle_packing_step

Topic: graphs   Node: 652de4259e86

Provenance: helper lemma. General form of the proved four-cycle digon reduction for OP-110.

A directed two-cycle can be added to any k-cycle packing theorem two outdegree units lower.
-/

theorem digraph_digon_cycle_packing_step
    (α : Type) [Fintype α] [DecidableEq α] (D : Digraph α) [DecidableRel D.Adj] (k d : ℕ)
    (hloop : ∀ v, ¬ D.Adj v v)
    (hdeg : ∀ v, d + 2 ≤ (Finset.univ.filter fun w => D.Adj v w).card)
    (hpack : ∀ T : Finset α, T.Nonempty →
      (∀ v ∈ T, d ≤ (T.filter fun w => D.Adj v w).card) →
      ∃ s : Fin k → Finset α, (∀ i, s i ⊆ T ∧ digraph_directed_cycle_on D (s i)) ∧
        Pairwise (fun i j => Disjoint (s i) (s j)))
    (u v : α) (huv : D.Adj u v) (hvu : D.Adj v u) :
    ∃ s : Fin (k + 1) → Finset α, (∀ i, digraph_directed_cycle_on D (s i)) ∧
      Pairwise (fun i j => Disjoint (s i) (s j)) := by
  classical
  have huvne : u ≠ v := by intro h; subst v; exact hloop u huv
  let T : Finset α := (Finset.univ.erase u).erase v
  let O : Finset α := Finset.univ.filter fun w => D.Adj u w
  have huO : u ∉ O := by simp [O, hloop]
  have hi : (insert u O).card ≤ (Finset.univ : Finset α).card :=
    Finset.card_le_card (Finset.subset_univ _)
  have hi' : (insert u O).card = O.card + 1 := Finset.card_insert_of_notMem huO
  have hd : d + 2 ≤ O.card := hdeg u
  have hcard : 3 ≤ (Finset.univ : Finset α).card := by omega
  have hT : T.Nonempty := by
    by_contra hn
    have he : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hn
    have hs : (Finset.univ : Finset α) ⊆ {u,v} := by
      intro x hx
      by_cases hxu : x = u
      · simp [hxu]
      by_cases hxv : x = v
      · simp [hxv]
      have : x ∈ T := by simp [T, hxu, hxv]
      rw [he] at this
      simp at this
    have hh := Finset.card_le_card hs
    have hp : ({u,v} : Finset α).card ≤ 2 := by simp [huvne]
    omega
  have hTdeg : ∀ x ∈ T, d ≤ (T.filter fun w => D.Adj x w).card := by
    intro x hx
    have hs : (Finset.univ.filter fun w => D.Adj x w) ⊆
        (T.filter fun w => D.Adj x w) ∪ {u,v} := by
      intro w hw
      have hadj := (Finset.mem_filter.mp hw).2
      by_cases hwu : w = u
      · simp [hwu]
      by_cases hwv : w = v
      · simp [hwv]
      have hwT : w ∈ T := by simp [T, hwu, hwv]
      exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hwT, hadj⟩)
    have hh := Finset.card_le_card hs
    have hu := Finset.card_union_le (T.filter fun w => D.Adj x w) ({u,v} : Finset α)
    have hp : ({u,v} : Finset α).card ≤ 2 := by simp [huvne]
    have hd := hdeg x
    omega
  obtain ⟨t, ht, hpair⟩ := hpack T hT hTdeg
  have h2 : digraph_directed_cycle_on D ({u,v} : Finset α) := by
    refine ⟨[u,v], ?_⟩
    simp [huvne, huv, hvu]
  have hdis : ∀ i, Disjoint ({u,v} : Finset α) (t i) := by
    intro i
    apply Finset.disjoint_left.mpr
    intro x hx hxt
    have hxT := (ht i).1 hxt
    simp only [T, Finset.mem_erase, Finset.mem_univ, and_true] at hxT
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> simp_all
  let f : Fin (k + 1) → Finset α := Fin.cases {u,v} t
  refine ⟨f, ?_, ?_⟩
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · exact h2
    · exact (ht i).2
  · intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · intro hij
        exact (hij rfl).elim
      · intro _
        exact hdis j
    · intro j
      refine Fin.cases ?_ (fun j => ?_) j
      · intro _
        exact (hdis i).symm
      · intro hij
        exact hpair (by simpa using hij)
