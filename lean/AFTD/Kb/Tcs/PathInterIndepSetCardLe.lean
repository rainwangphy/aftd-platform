import AFTD.Prelude

/-!
# path_inter_indep_set_card_le

Topic: graphs   Node: ba77a13bd1cd

Provenance: helper lemma. arXiv:2611.06362, Section 2.2, Equation (1)

Along any simple path in a simple graph G, the number of vertices lying in an independent set W is at most the number of vertices not in W plus one.
-/

lemma path_inter_indep_set_card_le_list {α : Type*} [DecidableEq α] (W : Finset α) (l : List α)
    (hchain : l.IsChain (fun a b => a ∈ W → b ∉ W)) :
    (l.filter (· ∈ W)).length ≤ (l.filter (· ∉ W)).length + 1 ∧
    (∀ a, l.head? = some a → a ∉ W → (l.filter (· ∈ W)).length ≤ (l.filter (· ∉ W)).length) := by
  induction l with
  | nil => simp
  | cons h t ih =>
    obtain ⟨ih1, ih2⟩ := ih hchain.tail
    by_cases hh : h ∈ W
    · have hpos : (h :: t).filter (· ∈ W) = h :: (t.filter (· ∈ W)) :=
        List.filter_cons_of_pos (decide_eq_true hh)
      have hneg : (h :: t).filter (· ∉ W) = t.filter (· ∉ W) :=
        List.filter_cons_of_neg (by simp [hh])
      have hhead : ∀ a, (h :: t).head? = some a → a ∉ W → ((h :: t).filter (· ∈ W)).length ≤ ((h :: t).filter (· ∉ W)).length := by
        intro a ha hna
        simp only [List.head?_cons, Option.some.injEq] at ha
        subst ha
        exact (hna hh).elim
      have hmain : ((h :: t).filter (· ∈ W)).length ≤ ((h :: t).filter (· ∉ W)).length + 1 := by
        rw [hpos, hneg, List.length_cons]
        cases t with
        | nil => simp
        | cons b t' =>
          have hrel := hchain.rel hh
          have hle := ih2 b rfl hrel
          omega
      exact ⟨hmain, hhead⟩
    · have hneg : (h :: t).filter (· ∈ W) = t.filter (· ∈ W) :=
        List.filter_cons_of_neg (by simp [hh])
      have hpos : (h :: t).filter (· ∉ W) = h :: (t.filter (· ∉ W)) :=
        List.filter_cons_of_pos (by simp [hh])
      have hhead : ∀ a, (h :: t).head? = some a → a ∉ W → ((h :: t).filter (· ∈ W)).length ≤ ((h :: t).filter (· ∉ W)).length := by
        intro a ha hna
        rw [hneg, hpos, List.length_cons]
        omega
      have hmain : ((h :: t).filter (· ∈ W)).length ≤ ((h :: t).filter (· ∉ W)).length + 1 := by
        have := hhead h rfl hh
        omega
      exact ⟨hmain, hhead⟩

/-- The intersection of any path's vertex set with an independent set has cardinality at most one more than the remaining vertices of the path. -/
lemma path_inter_indep_set_card_le {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {u v : V} (p : G.Walk u v) (hp : p.IsPath) (W : Finset V)
    (hW : G.IsIndepSet (W : Set V)) :
    (p.support.toFinset ∩ W).card ≤ (p.support.toFinset \ W).card + 1 := by
  have hnodup : p.support.Nodup := hp.support_nodup
  have hchain : p.support.IsChain G.Adj := p.isChain_adj_support
  have hchain' : p.support.IsChain (fun a b => a ∈ W → b ∉ W) := by
    apply hchain.imp
    intro a b hadj ha hb
    exact hW (Finset.mem_coe.mpr ha) (Finset.mem_coe.mpr hb) hadj.ne hadj
  have h_inter : (p.support.toFinset ∩ W).card = (p.support.filter (· ∈ W)).length := by
    rw [← List.toFinset_card_of_nodup (hnodup.filter _)]
    congr 1
    ext x
    simp
  have h_diff : (p.support.toFinset \ W).card = (p.support.filter (· ∉ W)).length := by
    rw [← List.toFinset_card_of_nodup (hnodup.filter _)]
    congr 1
    ext x
    simp
  rw [h_inter, h_diff]
  exact (path_inter_indep_set_card_le_list W p.support hchain').1
