import AFTD.Prelude
import AFTD.Kb.Optimization.BallBearingGraph

/-!
# ball_bearing_not_hamiltonian

Topic: integer_programming   Node: 54b308b2532b

Provenance: formalization of a published result. Source: arXiv:2611.17386 Lemma 2

For any integer k ≥ 3, the Ball Bearing graph ballBearingGraph k contains no Hamiltonian cycle, that is, ¬ (ballBearingGraph k).IsHamiltonian.
-/

/-- For any integer k ≥ 3, the Ball Bearing graph BB(k) contains no Hamiltonian cycle. -/
theorem ball_bearing_not_hamiltonian {k : ℕ} (hk : 3 ≤ k) :
    ¬ (ballBearingGraph k).IsHamiltonian := by
  intro hHam
  haveI : NeZero k := ⟨by omega⟩
  have hmod1 : 1 % k = 1 := Nat.mod_eq_of_lt (by omega)
  have hadd1 : ∀ (a : Fin k), a + 1 = (⟨(a.val + 1) % k, Nat.mod_lt _ (by omega)⟩ : Fin k) := by
    intro a; ext
    rw [Fin.val_add]
    simp only [Fin.val_one', hmod1]
  have hnext : ∀ (a b : Fin k), (a + 1 = b) ↔ ((a.val + 1) % k = b.val) := by
    intro a b
    rw [hadd1 a, Fin.ext_iff]
  have hadj : ∀ x y : Fin k × Fin 5, (ballBearingGraph k).Adj x y ↔ x ≠ y ∧
      ((x.1 = y.1 ∧ (x.2 = 0 ∧ y.2 = 1 ∨ x.2 = 1 ∧ y.2 = 0 ∨ x.2 = 1 ∧ y.2 = 2 ∨ x.2 = 2 ∧ y.2 = 1 ∨ x.2 = 1 ∧ y.2 = 3 ∨ x.2 = 3 ∧ y.2 = 1 ∨ x.2 = 2 ∧ y.2 = 3 ∨ x.2 = 3 ∧ y.2 = 2 ∨ x.2 = 3 ∧ y.2 = 4 ∨ x.2 = 4 ∧ y.2 = 3)) ∨
      (x.1 + 1 = y.1 ∧ (x.2 = 0 ∧ y.2 = 0 ∨ x.2 = 1 ∧ y.2 = 0 ∨ x.2 = 4 ∧ y.2 = 2)) ∨
      (y.1 + 1 = x.1 ∧ (y.2 = 0 ∧ x.2 = 0 ∨ y.2 = 1 ∧ x.2 = 0 ∨ y.2 = 4 ∧ x.2 = 2))) := by
    intro x y
    simp only [ballBearingGraph]
    refine ⟨fun ⟨h, h'⟩ => ⟨h, ?_⟩, fun ⟨h, h'⟩ => ⟨h, ?_⟩⟩
    · rcases h' with h' | h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl ⟨(hnext x.1 y.1).mpr h'.1, h'.2⟩)
      · exact Or.inr (Or.inr ⟨(hnext y.1 x.1).mpr h'.1, h'.2⟩)
    · rcases h' with h' | h' | h'
      · exact Or.inl h'
      · exact Or.inr (Or.inl ⟨(hnext x.1 y.1).mp h'.1, h'.2⟩)
      · exact Or.inr (Or.inr ⟨(hnext y.1 x.1).mp h'.1, h'.2⟩)
  have hne_succ : ∀ j : Fin k, j + 1 ≠ j := by
    intro j h
    have h1 : (j.val + 1) % k = j.val := (hnext j j).mp h
    have h2 : j.val + 1 ≤ k := by have := j.isLt; omega
    rcases Nat.lt_or_eq_of_le h2 with h3 | h3
    · rw [Nat.mod_eq_of_lt h3] at h1; omega
    · rw [h3, Nat.mod_self] at h1; omega
  have hp01 : ∀ j : Fin k, ((j, (0:Fin 5)) : Fin k × Fin 5) ≠ (j + 1, 0) := by
    intro j h
    exact hne_succ j (congrArg Prod.fst h).symm
  haveI : Nontrivial (Fin k × Fin 5) :=
    ⟨⟨((0:Fin k), (0:Fin 5)), ((0:Fin k), (1:Fin 5)), by simp⟩⟩
  obtain ⟨p, hp⟩ := hHam.exists_isHamiltonianCycle ((0:Fin k), (0:Fin 5))
  let H : (ballBearingGraph k).Subgraph := p.toSubgraph
  have hdeg : ∀ v : Fin k × Fin 5, (H.neighborSet v).ncard = 2 :=
    fun v => hp.toIsCycle.ncard_neighborSet_toSubgraph_eq_two (hp.mem_support v)
  have hsub : ∀ v w, H.Adj v w → (ballBearingGraph k).Adj v w := fun v w h => H.adj_sub h
  have L4 : ∀ j : Fin k, (ballBearingGraph k).neighborSet (j, 4) = {(j, 3), (j + 1, 2)} := by
    intro j
    ext w
    obtain ⟨i, s⟩ := w
    fin_cases s <;> simp [hadj, SimpleGraph.mem_neighborSet, eq_comm]
  have L3 : ∀ j : Fin k, (ballBearingGraph k).neighborSet (j, 3) ⊆ {(j,1),(j,2),(j,4)} := by
    intro j w hw
    obtain ⟨i, s⟩ := w
    fin_cases s <;> simp [hadj, SimpleGraph.mem_neighborSet, eq_comm] at hw ⊢ <;> tauto
  have L2 : ∀ j : Fin k, (ballBearingGraph k).neighborSet (j, 2) ⊆ {(j,1),(j,3),(j-1,4)} := by
    intro j w hw
    obtain ⟨i, s⟩ := w
    fin_cases s <;> simp [hadj, SimpleGraph.mem_neighborSet, eq_comm, eq_sub_iff_add_eq] at hw ⊢ <;> tauto
  have L1 : ∀ j : Fin k, (ballBearingGraph k).neighborSet (j, 1) ⊆ {(j,0),(j,2),(j,3),(j+1,0)} := by
    intro j w hw
    obtain ⟨i, s⟩ := w
    fin_cases s <;> simp [hadj, SimpleGraph.mem_neighborSet, eq_comm] at hw ⊢ <;> tauto
  have L0 : ∀ j : Fin k, (ballBearingGraph k).neighborSet (j, 0) ⊆ {(j,1),(j+1,0),(j-1,0),(j-1,1)} := by
    intro j w hw
    obtain ⟨i, s⟩ := w
    fin_cases s <;> simp [hadj, SimpleGraph.mem_neighborSet, eq_comm, eq_sub_iff_add_eq] at hw ⊢ <;> tauto
  have ncard3 : ∀ a b c : Fin k × Fin 5, a ≠ b → a ≠ c → b ≠ c →
      ({a, b, c} : Set (Fin k × Fin 5)).ncard = 3 := by
    intro a b c hab hac hbc
    have h1 : a ∉ ({b, c} : Set (Fin k × Fin 5)) := by simp [hab, hac]
    have h2 : b ∉ ({c} : Set (Fin k × Fin 5)) := by simp [hbc]
    rw [show ({a,b,c} : Set (Fin k × Fin 5)) = insert a (insert b {c}) from rfl,
      Set.ncard_insert_of_notMem h1, Set.ncard_insert_of_notMem h2, Set.ncard_singleton]
  have hA4 : ∀ j : Fin k, H.Adj (j, 4) (j, 3) ∧ H.Adj (j, 4) (j + 1, 2) := by
    intro j
    have heq : H.neighborSet (j, 4) = ({(j, 3), (j + 1, 2)} : Set (Fin k × Fin 5)) := by
      refine Set.eq_of_subset_of_ncard_le ?_ ?_
      · intro w hw
        have hw' : w ∈ (ballBearingGraph k).neighborSet (j, 4) := hsub _ _ hw
        rwa [L4 j] at hw'
      · rw [Set.ncard_pair (by simp), hdeg]
    constructor
    · have h : (j, 3) ∈ H.neighborSet (j, 4) := by rw [heq]; simp
      exact h
    · have h : ((j + 1, 2) : Fin k × Fin 5) ∈ H.neighborSet (j, 4) := by rw [heq]; simp
      exact h
  have hE3a : ∀ j : Fin k, ¬(H.Adj (j, 3) (j, 1) ∧ H.Adj (j, 3) (j, 2)) := by
    intro j hb
    have hsub' : ({(j, 1), (j, 2), (j, 4)} : Set (Fin k × Fin 5)) ⊆ H.neighborSet (j, 3) := by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact hb.1
      · exact hb.2
      · exact (hA4 j).1.symm
    have h3 : ({(j, 1), (j, 2), (j, 4)} : Set (Fin k × Fin 5)).ncard = 3 :=
      ncard3 _ _ _ (by simp) (by simp) (by simp)
    have hle := Set.ncard_le_ncard hsub'
    rw [h3, hdeg] at hle
    omega
  have hE3b : ∀ j : Fin k, H.Adj (j, 3) (j, 1) ∨ H.Adj (j, 3) (j, 2) := by
    intro j
    by_contra hc
    push_neg at hc
    obtain ⟨hc1, hc2⟩ := hc
    have hsub' : H.neighborSet (j, 3) ⊆ ({(j, 4)} : Set (Fin k × Fin 5)) := by
      intro x hx
      have hxG : x ∈ (ballBearingGraph k).neighborSet (j, 3) := hsub _ _ hx
      have hxG' := L3 j hxG
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxG' ⊢
      rcases hxG' with rfl | rfl | rfl
      · exact absurd hx hc1
      · exact absurd hx hc2
      · rfl
    have hle := Set.ncard_le_ncard hsub'
    rw [Set.ncard_singleton, hdeg] at hle
    omega
  have hprev : ∀ j : Fin k, H.Adj (j, 2) ((j - 1, 4) : Fin k × Fin 5) := by
    intro j
    have h := (hA4 (j - 1)).2
    rw [sub_add_cancel] at h
    exact h.symm
  have hE2a : ∀ j : Fin k, ¬(H.Adj (j, 2) (j, 1) ∧ H.Adj (j, 2) (j, 3)) := by
    intro j hb
    have hsub' : ({(j, 1), (j, 3), (j - 1, 4)} : Set (Fin k × Fin 5)) ⊆ H.neighborSet (j, 2) := by
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact hb.1
      · exact hb.2
      · exact hprev j
    have h3 : ({(j, 1), (j, 3), (j - 1, 4)} : Set (Fin k × Fin 5)).ncard = 3 :=
      ncard3 _ _ _ (by simp) (by simp) (by simp)
    have hle := Set.ncard_le_ncard hsub'
    rw [h3, hdeg] at hle
    omega
  have hE2b : ∀ j : Fin k, H.Adj (j, 2) (j, 1) ∨ H.Adj (j, 2) (j, 3) := by
    intro j
    by_contra hc
    push_neg at hc
    obtain ⟨hc1, hc2⟩ := hc
    have hsub' : H.neighborSet (j, 2) ⊆ ({(j - 1, 4)} : Set (Fin k × Fin 5)) := by
      intro x hx
      have hxG : x ∈ (ballBearingGraph k).neighborSet (j, 2) := hsub _ _ hx
      have hxG' := L2 j hxG
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxG' ⊢
      rcases hxG' with rfl | rfl | rfl
      · exact absurd hx hc1
      · exact absurd hx hc2
      · rfl
    have hle := Set.ncard_le_ncard hsub'
    rw [Set.ncard_singleton, hdeg] at hle
    omega
  have hb1 : ∀ j : Fin k, H.Adj (j, 2) (j, 3) →
      H.neighborSet (j, 1) = ({(j, 0), (j + 1, 0)} : Set (Fin k × Fin 5)) := by
    intro j hb
    have hn2 : ¬ H.Adj (j, 1) (j, 2) := fun h => (hE2a j) ⟨h.symm, hb⟩
    have hn3 : ¬ H.Adj (j, 1) (j, 3) := fun h => (hE3a j) ⟨h.symm, hb.symm⟩
    refine Set.eq_of_subset_of_ncard_le ?_ ?_
    · intro x hx
      have hxG : x ∈ (ballBearingGraph k).neighborSet (j, 1) := hsub _ _ hx
      have hxG' := L1 j hxG
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxG' ⊢
      rcases hxG' with rfl | rfl | rfl | rfl
      · simp
      · exact absurd hx hn2
      · exact absurd hx hn3
      · simp
    · rw [Set.ncard_pair (hp01 j), hdeg]
  have hb2 : ∀ j : Fin k, ¬ H.Adj (j, 2) (j, 3) →
      H.neighborSet (j, 1) = ({(j, 2), (j, 3)} : Set (Fin k × Fin 5)) := by
    intro j hb
    have hp12 : H.Adj (j, 1) (j, 2) := by
      rcases hE2b j with h | h
      · exact h.symm
      · exact absurd h hb
    have hp13 : H.Adj (j, 1) (j, 3) := by
      rcases hE3b j with h | h
      · exact h.symm
      · exact absurd h.symm hb
    have h := Set.eq_of_subset_of_ncard_le
      (s := ({(j, 2), (j, 3)} : Set (Fin k × Fin 5))) (t := H.neighborSet (j, 1)) ?_ ?_
    · exact h.symm
    · intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl
      · exact hp12
      · exact hp13
    · rw [Set.ncard_pair (by simp), hdeg]
  let b : Fin k → Prop := fun j => H.Adj (j, 2) (j, 3)
  let Z : Set (Fin k × Fin 5) := {v | (∃ j, v = (j, (0:Fin 5))) ∨ (∃ j, v = (j, (1:Fin 5)) ∧ b j)}
  have hclos : ∀ v ∈ Z, ∀ w, H.Adj v w → w ∈ Z := by
    intro v hv w hw
    rcases hv with ⟨j, rfl⟩ | ⟨j, rfl, hj⟩
    · obtain ⟨i, s⟩ := w
      have hwG : ((i, s) : Fin k × Fin 5) ∈ (ballBearingGraph k).neighborSet (j, 0) := hsub _ _ hw
      have hwG' := L0 j hwG
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hwG'
      rcases hwG' with h1 | h1 | h1 | h1
      · rw [h1] at hw ⊢
        refine Or.inr ⟨j, rfl, ?_⟩
        by_contra hnb
        have h := hb2 j hnb
        have hmem : ((j, (0:Fin 5)) : Fin k × Fin 5) ∈ H.neighborSet (j, 1) := hw.symm
        rw [h] at hmem
        simp at hmem
      · rw [h1]; exact Or.inl ⟨j + 1, rfl⟩
      · rw [h1]; exact Or.inl ⟨j - 1, rfl⟩
      · rw [h1] at hw ⊢
        refine Or.inr ⟨j - 1, rfl, ?_⟩
        by_contra hnb
        have h := hb2 (j - 1) hnb
        have hmem : ((j, (0:Fin 5)) : Fin k × Fin 5) ∈ H.neighborSet (j - 1, 1) := hw.symm
        rw [h] at hmem
        simp at hmem
    · have h := hb1 j hj
      have hmem : w ∈ H.neighborSet (j, 1) := hw
      rw [h] at hmem
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with h1 | h1
      · rw [h1]; exact Or.inl ⟨j, rfl⟩
      · rw [h1]; exact Or.inl ⟨j + 1, rfl⟩
  have h0Z : ((0:Fin k), (0:Fin 5)) ∈ Z := Or.inl ⟨0, rfl⟩
  have h2Z : ((0:Fin k), (2:Fin 5)) ∉ Z := by
    intro h
    rcases h with ⟨j, hj⟩ | ⟨j, hj, _⟩
    · simp at hj
    · simp at hj
  have key : ∀ i : ℕ, i ≤ p.length → p.getVert i ∈ Z := by
    intro i
    induction i with
    | zero => intro _; rw [SimpleGraph.Walk.getVert_zero]; exact h0Z
    | succ n ih =>
      intro hn
      have hprev : n ≤ p.length := by omega
      have hnlt : n < p.length := by omega
      exact hclos _ (ih hprev) _ (p.toSubgraph_adj_getVert hnlt)
  obtain ⟨i, hi, hile⟩ :=
    SimpleGraph.Walk.mem_support_iff_exists_getVert.mp (hp.mem_support ((0:Fin k), (2:Fin 5)))
  exact h2Z (hi ▸ key i hile)
