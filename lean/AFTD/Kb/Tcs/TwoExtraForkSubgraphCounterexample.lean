import AFTD.Prelude

/-!
# two_extra_fork_subgraph_counterexample

Topic: graphs   Node: aafa348877e9

Provenance: helper lemma. Refutes the partial-fork subgraph lemma using the explicit eight-vertex graph in experiment 16921.

There is a triangle-free graph on four pairs whose edges lie in the union of one fork per pair and two additional forks, but whose independence number is less than four.
-/

set_option maxRecDepth 100000
set_option maxHeartbeats 1000000

abbrev V580 := Fin 4 × Fin 2

def name580 (v : V580) : Fin 8 :=
  ![![0,7], ![1,4], ![2,3], ![5,6]] v.1 v.2

def edges580 : List (Fin 8 × Fin 8) :=
  [(0,3),(0,4),(1,2),(1,5),(2,6),(2,4),(3,6),(4,7),(5,7),(6,7)]

def graph580 : SimpleGraph V580 where
  Adj x y := x ≠ y ∧ ((name580 x, name580 y) ∈ edges580 ∨ (name580 y, name580 x) ∈ edges580)
  symm := ⟨by intro x y h; exact ⟨h.1.symm, h.2.symm⟩⟩
  loopless := ⟨by intro x h; exact h.1 rfl⟩

instance : DecidableRel graph580.Adj := fun x y => inferInstanceAs (Decidable (x ≠ y ∧ _))

def w580 : Fin 4 → V580 := ![(2,1),(2,0),(3,1),(1,0)]

theorem hw580 : ∀ i, (w580 i).1 ≠ i := by decide

theorem cover580 : ∀ x y, graph580.Adj x y →
    (∃ i : Fin 4, (x.1 = i ∧ y = w580 i) ∨ (y.1 = i ∧ x = w580 i)) ∨
    (x.1 = 0 ∧ y = (1,1)) ∨ (y.1 = 0 ∧ x = (1,1)) ∨
    (x.1 = 3 ∧ y = (0,1)) ∨ (y.1 = 3 ∧ x = (0,1)) := by decide

theorem notriangle580 : ∀ a b c : V580,
    graph580.Adj a b → graph580.Adj b c → ¬ graph580.Adj a c := by
  decide

theorem trianglefree580 : graph580.CliqueFree 3 := by
  intro s hs
  rw [SimpleGraph.isNClique_iff] at hs
  obtain ⟨hc, hs⟩ := hs
  obtain ⟨a,b,c,hab,hac,hbc,rfl⟩ := Finset.card_eq_three.mp hs
  exact notriangle580 a b c (hc (by simp) (by simp) hab) (hc (by simp) (by simp) hbc)
    (hc (by simp) (by simp) hac)

theorem nofour580 : ¬∃ I : Finset V580, 4 ≤ I.card ∧ graph580.IsIndepSet (I : Set V580) := by
  classical
  intro ⟨I, hcard, hi⟩
  have hc : I.card = ∑ v : V580, if v ∈ I then 1 else 0 := by simp
  rw [Fintype.sum_prod_type] at hc
  simp only [Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero] at hc
  have e03 : ¬ (((0,0) : V580) ∈ I ∧ ((2,1) : V580) ∈ I) := by
    rintro ⟨ha, hb⟩
    exact (hi ha hb (by decide)) (by decide)
  have e04 : ¬ (((0,0) : V580) ∈ I ∧ ((1,1) : V580) ∈ I) := by
    rintro ⟨ha, hb⟩
    exact (hi ha hb (by decide)) (by decide)
  have e12 : ¬ (((1,0) : V580) ∈ I ∧ ((2,0) : V580) ∈ I) := by
    rintro ⟨ha, hb⟩
    exact (hi ha hb (by decide)) (by decide)
  have e15 : ¬ (((1,0) : V580) ∈ I ∧ ((3,0) : V580) ∈ I) := by
    rintro ⟨ha, hb⟩
    exact (hi ha hb (by decide)) (by decide)
  have e26 : ¬ (((2,0) : V580) ∈ I ∧ ((3,1) : V580) ∈ I) := by
    rintro ⟨ha, hb⟩
    exact (hi ha hb (by decide)) (by decide)
  have e24 : ¬ (((2,0) : V580) ∈ I ∧ ((1,1) : V580) ∈ I) := by
    rintro ⟨ha, hb⟩
    exact (hi ha hb (by decide)) (by decide)
  have e36 : ¬ (((2,1) : V580) ∈ I ∧ ((3,1) : V580) ∈ I) := by
    rintro ⟨ha, hb⟩
    exact (hi ha hb (by decide)) (by decide)
  have e47 : ¬ (((1,1) : V580) ∈ I ∧ ((0,1) : V580) ∈ I) := by
    rintro ⟨ha, hb⟩
    exact (hi ha hb (by decide)) (by decide)
  have e57 : ¬ (((3,0) : V580) ∈ I ∧ ((0,1) : V580) ∈ I) := by
    rintro ⟨ha, hb⟩
    exact (hi ha hb (by decide)) (by decide)
  have e67 : ¬ (((3,1) : V580) ∈ I ∧ ((0,1) : V580) ∈ I) := by
    rintro ⟨ha, hb⟩
    exact (hi ha hb (by decide)) (by decide)
  by_cases h0 : ((0,0) : V580) ∈ I <;>
  by_cases h1 : ((1,0) : V580) ∈ I <;>
  by_cases h2 : ((2,0) : V580) ∈ I <;>
  by_cases h3 : ((2,1) : V580) ∈ I <;>
  by_cases h4 : ((1,1) : V580) ∈ I <;>
  by_cases h5 : ((3,0) : V580) ∈ I <;>
  by_cases h6 : ((3,1) : V580) ∈ I <;>
  by_cases h7 : ((0,1) : V580) ∈ I <;>
  simp_all <;> omega

theorem two_extra_fork_subgraph_counterexample :
    ∃ (G : SimpleGraph (Fin 4 × Fin 2)) (w : Fin 4 → Fin 4 × Fin 2),
      (∀ i, (w i).1 ≠ i) ∧
      (∀ x y, G.Adj x y →
        (∃ i : Fin 4, (x.1 = i ∧ y = w i) ∨ (y.1 = i ∧ x = w i)) ∨
        (x.1 = 0 ∧ y = (1,1)) ∨ (y.1 = 0 ∧ x = (1,1)) ∨
        (x.1 = 3 ∧ y = (0,1)) ∨ (y.1 = 3 ∧ x = (0,1))) ∧
      G.CliqueFree 3 ∧
      ¬∃ I : Finset (Fin 4 × Fin 2), 4 ≤ I.card ∧ G.IsIndepSet (I : Set (Fin 4 × Fin 2)) := by
  exact ⟨graph580, w580, hw580, cover580, trianglefree580, nofour580⟩
