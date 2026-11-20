import AFTD.Prelude
import AFTD.Kb.Tcs.IsKExtendable
import AFTD.Kb.Tcs.UniquelyK4SaturatedMaxDegreeSixOrderTwelve

/-!
# op1957_short_extendibility_hypothesis_is_necessary

Topic: graphs   Node: b5478a59c490

Provenance: helper lemma. Explicit counterexample to extendable_forbids_connected_three_vertex_twin_cut; experiment 35108.

A connected 2-extendible but not 3-extendible graph on ten vertices has disjoint three-vertex sets T,N, with T a clique complete to the connected four-vertex complement of T ∪ N and anticomplete to N, while N minus vertex 7 has a perfect matching. This refutes the unrestricted connected-three-vertex-twin-cut lemma, whose proof requires shorter extendibility.
-/

def op1957_replacement_counterexample_base (a b : Fin 10) : Prop :=
  (a.val < 3 ∧ b.val < 3) ∨
  (a.val < 3 ∧ 3 ≤ b.val ∧ b.val < 7) ∨
  ((3 ≤ a.val ∧ a.val < 7) ∧ 7 ≤ b.val) ∨
  (7 ≤ a.val ∧ 7 ≤ b.val) ∨
  (a.val = 3 ∧ 3 ≤ b.val ∧ b.val < 7)

def op1957_replacement_counterexample_G : SimpleGraph (Fin 10) where
  Adj a b := a ≠ b ∧ (op1957_replacement_counterexample_base a b ∨ op1957_replacement_counterexample_base b a)
  symm := ⟨by intro a b h; exact ⟨h.1.symm, h.2.elim Or.inr Or.inl⟩⟩
  loopless := ⟨by intro a h; exact h.1 rfl⟩

instance : DecidableRel op1957_replacement_counterexample_G.Adj := fun a b => by
  change Decidable (a ≠ b ∧ (op1957_replacement_counterexample_base a b ∨ op1957_replacement_counterexample_base b a))
  unfold op1957_replacement_counterexample_base
  infer_instance

open Sym2

/-- The 33 edges of the counterexample graph. -/
def op1957_short_extendibility_hypothesis_is_necessary_allEdges : Finset (Sym2 (Fin 10)) := {
  s(0,1), s(0,2), s(0,3), s(0,4), s(0,5), s(0,6), s(1,2), s(1,3), s(1,4), s(1,5), s(1,6),
  s(2,3), s(2,4), s(2,5), s(2,6), s(3,4), s(3,5), s(3,6), s(3,7), s(3,8), s(3,9),
  s(4,7), s(4,8), s(4,9), s(5,7), s(5,8), s(5,9), s(6,7), s(6,8), s(6,9), s(7,8), s(7,9), s(8,9)}

/-- A 55-element family of perfect matchings covering every 2-edge matching. -/
def op1957_short_extendibility_hypothesis_is_necessary_pme : Fin 55 → Finset (Sym2 (Fin 10)) := ![
  {s(0,1), s(2,3), s(4,7), s(5,8), s(6,9)}, {s(0,1), s(2,4), s(3,5), s(6,7), s(8,9)},
  {s(0,1), s(2,5), s(3,4), s(6,8), s(7,9)}, {s(0,1), s(2,6), s(3,7), s(4,8), s(5,9)},
  {s(0,2), s(1,3), s(4,7), s(5,9), s(6,8)}, {s(0,2), s(1,4), s(3,5), s(6,9), s(7,8)},
  {s(0,2), s(1,5), s(3,6), s(4,8), s(7,9)}, {s(0,2), s(1,6), s(3,4), s(5,7), s(8,9)},
  {s(0,3), s(1,2), s(4,8), s(5,7), s(6,9)}, {s(0,3), s(1,4), s(2,6), s(5,8), s(7,9)},
  {s(0,3), s(1,6), s(2,4), s(5,9), s(7,8)}, {s(0,4), s(1,2), s(3,8), s(5,9), s(6,7)},
  {s(0,4), s(1,5), s(2,6), s(3,9), s(7,8)}, {s(0,5), s(1,2), s(3,6), s(4,7), s(8,9)},
  {s(0,6), s(1,2), s(3,7), s(4,9), s(5,8)}, {s(0,1), s(2,5), s(3,6), s(4,9), s(7,8)},
  {s(0,4), s(1,6), s(2,5), s(3,7), s(8,9)}, {s(0,5), s(1,6), s(2,3), s(4,8), s(7,9)},
  {s(0,6), s(1,4), s(2,3), s(5,7), s(8,9)}, {s(0,6), s(1,5), s(2,4), s(3,8), s(7,9)},
  {s(0,1), s(2,4), s(3,9), s(5,7), s(6,8)}, {s(0,2), s(1,3), s(4,9), s(5,8), s(6,7)},
  {s(0,4), s(1,2), s(3,5), s(6,8), s(7,9)}, {s(0,5), s(1,3), s(2,4), s(6,9), s(7,8)},
  {s(0,1), s(2,6), s(3,8), s(4,9), s(5,7)}, {s(0,3), s(1,5), s(2,6), s(4,7), s(8,9)},
  {s(0,6), s(1,2), s(3,4), s(5,9), s(7,8)}, {s(0,6), s(1,3), s(2,5), s(4,8), s(7,9)},
  {s(0,2), s(1,5), s(3,7), s(4,9), s(6,8)}, {s(0,2), s(1,6), s(3,9), s(4,7), s(5,8)},
  {s(0,5), s(1,2), s(3,9), s(4,8), s(6,7)}, {s(0,1), s(2,5), s(3,8), s(4,7), s(6,9)},
  {s(0,3), s(1,4), s(2,5), s(6,7), s(8,9)}, {s(0,4), s(1,3), s(2,6), s(5,7), s(8,9)},
  {s(0,4), s(1,5), s(2,3), s(6,9), s(7,8)}, {s(0,5), s(1,4), s(2,3), s(6,8), s(7,9)},
  {s(0,1), s(2,4), s(3,6), s(5,8), s(7,9)}, {s(0,2), s(1,4), s(3,6), s(5,9), s(7,8)},
  {s(0,2), s(1,5), s(3,4), s(6,7), s(8,9)}, {s(0,2), s(1,6), s(3,5), s(4,9), s(7,8)},
  {s(0,5), s(1,4), s(2,6), s(3,7), s(8,9)}, {s(0,6), s(1,2), s(3,5), s(4,7), s(8,9)},
  {s(0,6), s(1,4), s(2,5), s(3,9), s(7,8)}, {s(0,1), s(2,3), s(4,8), s(5,9), s(6,7)},
  {s(0,1), s(2,4), s(3,7), s(5,8), s(6,9)}, {s(0,1), s(2,6), s(3,4), s(5,8), s(7,9)},
  {s(0,1), s(2,6), s(3,5), s(4,8), s(7,9)}, {s(0,2), s(1,4), s(3,8), s(5,7), s(6,9)},
  {s(0,3), s(1,2), s(4,9), s(5,7), s(6,8)}, {s(0,4), s(1,2), s(3,6), s(5,7), s(8,9)},
  {s(0,5), s(1,2), s(3,4), s(6,9), s(7,8)}, {s(0,5), s(1,2), s(3,8), s(4,9), s(6,7)},
  {s(0,1), s(2,3), s(4,9), s(5,7), s(6,8)}, {s(0,2), s(1,6), s(3,8), s(4,7), s(5,9)},
  {s(0,4), s(1,2), s(3,6), s(5,8), s(7,9)}]

lemma op1957_short_extendibility_hypothesis_is_necessary_allEdges_eq :
    ∀ e : Sym2 (Fin 10),
      e ∈ op1957_short_extendibility_hypothesis_is_necessary_allEdges ↔
      e ∈ op1957_replacement_counterexample_G.edgeSet := by
  decide

lemma op1957_short_extendibility_hypothesis_is_necessary_pme_adj :
    ∀ i : Fin 55, ∀ a b : Fin 10,
      s(a,b) ∈ op1957_short_extendibility_hypothesis_is_necessary_pme i →
      op1957_replacement_counterexample_G.Adj a b := by
  decide

lemma op1957_short_extendibility_hypothesis_is_necessary_cover :
    ∀ a b c d : Fin 10,
      s(a,b) ∈ op1957_short_extendibility_hypothesis_is_necessary_allEdges →
      s(c,d) ∈ op1957_short_extendibility_hypothesis_is_necessary_allEdges →
      (∀ v : Fin 10, v ∈ s(a,b) → v ∈ s(c,d) → False) →
      ∃ i : Fin 55, s(a,b) ∈ op1957_short_extendibility_hypothesis_is_necessary_pme i ∧
        s(c,d) ∈ op1957_short_extendibility_hypothesis_is_necessary_pme i := by
  decide

/-- The perfect matching subgraph associated with a covering family member. -/
def op1957_short_extendibility_hypothesis_is_necessary_pmSub (i : Fin 55) :
    op1957_replacement_counterexample_G.Subgraph where
  verts := Set.univ
  Adj a b := s(a, b) ∈ op1957_short_extendibility_hypothesis_is_necessary_pme i
  adj_sub := fun h => op1957_short_extendibility_hypothesis_is_necessary_pme_adj i _ _ h
  edge_vert := fun _ => Set.mem_univ _
  symm := ⟨fun a b h =>
    (Sym2.eq_swap (a := a) (b := b)) ▸ h⟩

lemma op1957_short_extendibility_hypothesis_is_necessary_pmSub_perfect :
    ∀ i : Fin 55,
      (op1957_short_extendibility_hypothesis_is_necessary_pmSub i).IsPerfectMatching := by
  unfold op1957_short_extendibility_hypothesis_is_necessary_pmSub
    SimpleGraph.Subgraph.IsPerfectMatching SimpleGraph.Subgraph.IsMatching
    SimpleGraph.Subgraph.IsSpanning
  decide

/-- A subgraph from a vertex set and a finite edge set. -/
def op1957_short_extendibility_hypothesis_is_necessary_mk (s : Finset (Fin 10))
    (E : Finset (Sym2 (Fin 10)))
    (hE : ∀ a b : Fin 10, s(a,b) ∈ E → op1957_replacement_counterexample_G.Adj a b)
    (hs : ∀ a b : Fin 10, s(a,b) ∈ E → a ∈ s) :
    op1957_replacement_counterexample_G.Subgraph where
  verts := ↑s
  Adj a b := s(a, b) ∈ E
  adj_sub := fun h => hE _ _ h
  edge_vert := fun h => Finset.mem_coe.mpr (hs _ _ h)
  symm := ⟨fun a b h => (Sym2.eq_swap (a := a) (b := b)) ▸ h⟩

lemma op1957_short_extendibility_hypothesis_is_necessary_mk_edgeSet (s : Finset (Fin 10))
    (E : Finset (Sym2 (Fin 10)))
    (hE : ∀ a b : Fin 10, s(a,b) ∈ E → op1957_replacement_counterexample_G.Adj a b)
    (hs : ∀ a b : Fin 10, s(a,b) ∈ E → a ∈ s) :
    (op1957_short_extendibility_hypothesis_is_necessary_mk s E hE hs).edgeSet =
      (E : Set (Sym2 (Fin 10))) := by
  ext e
  induction e using Sym2.ind with
  | h a b => exact Iff.rfl

lemma op1957_short_extendibility_hypothesis_is_necessary_mk_ncard (s : Finset (Fin 10))
    (E : Finset (Sym2 (Fin 10)))
    (hE : ∀ a b : Fin 10, s(a,b) ∈ E → op1957_replacement_counterexample_G.Adj a b)
    (hs : ∀ a b : Fin 10, s(a,b) ∈ E → a ∈ s) :
    (op1957_short_extendibility_hypothesis_is_necessary_mk s E hE hs).edgeSet.ncard = E.card := by
  rw [op1957_short_extendibility_hypothesis_is_necessary_mk_edgeSet, Set.ncard_coe_finset]

/-- The two-edge matching {0-3, 1-2}. -/
def op1957_short_extendibility_hypothesis_is_necessary_M2 :
    op1957_replacement_counterexample_G.Subgraph :=
  op1957_short_extendibility_hypothesis_is_necessary_mk {0,1,2,3} {s(0,3), s(1,2)}
    (by decide) (by decide)

lemma op1957_short_extendibility_hypothesis_is_necessary_M2_matching :
    op1957_short_extendibility_hypothesis_is_necessary_M2.IsMatching := by
  show (op1957_short_extendibility_hypothesis_is_necessary_mk {0,1,2,3} {s(0,3), s(1,2)}
    (by decide) (by decide)).IsMatching
  unfold op1957_short_extendibility_hypothesis_is_necessary_mk SimpleGraph.Subgraph.IsMatching
  decide

lemma op1957_short_extendibility_hypothesis_is_necessary_M2_card :
    op1957_short_extendibility_hypothesis_is_necessary_M2.edgeSet.ncard = 2 := by
  show (op1957_short_extendibility_hypothesis_is_necessary_mk {0,1,2,3} {s(0,3), s(1,2)}
    (by decide) (by decide)).edgeSet.ncard = 2
  rw [op1957_short_extendibility_hypothesis_is_necessary_mk_ncard]
  decide

/-- Two distinct edges of a matching have disjoint endpoints. -/
lemma op1957_short_extendibility_hypothesis_is_necessary_edges_disjoint
    (M : op1957_replacement_counterexample_G.Subgraph) (hM : M.IsMatching)
    {a b c d : Fin 10} (h1 : M.Adj a b) (h2 : M.Adj c d) (hne : s(a,b) ≠ s(c,d)) :
    a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d := by
  have key : ∀ {x y z : Fin 10}, M.Adj x y → M.Adj x z → y = z :=
    fun hy hz => (hM (M.edge_vert hy)).unique hy hz
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro h; subst h; exact hne (by rw [key h1 h2])
  · intro h; subst h; exact hne (by rw [key h1 h2.symm, Sym2.eq_swap])
  · intro h; subst h; exact hne (by rw [key h1.symm h2, Sym2.eq_swap])
  · intro h; subst h; exact hne (by rw [key h1.symm h2.symm])

lemma op1957_short_extendibility_hypothesis_is_necessary_two :
    is_k_extendable op1957_replacement_counterexample_G 2 := by
  unfold is_k_extendable
  refine ⟨by decide, ⟨op1957_short_extendibility_hypothesis_is_necessary_M2,
    op1957_short_extendibility_hypothesis_is_necessary_M2_matching,
    op1957_short_extendibility_hypothesis_is_necessary_M2_card⟩, ?_⟩
  intro M hM hcard
  obtain ⟨e1, e2, hne, hset⟩ := Set.ncard_eq_two.mp hcard
  induction e1 using Sym2.ind with
  | h a b =>
  induction e2 using Sym2.ind with
  | h c d =>
  have h1mem : s(a,b) ∈ M.edgeSet := by rw [hset]; simp
  have h2mem : s(c,d) ∈ M.edgeSet := by rw [hset]; simp
  have hdisj4 := op1957_short_extendibility_hypothesis_is_necessary_edges_disjoint M hM
    (SimpleGraph.Subgraph.mem_edgeSet.mp h1mem) (SimpleGraph.Subgraph.mem_edgeSet.mp h2mem) hne
  have hdisj : ∀ v : Fin 10, v ∈ s(a,b) → v ∈ s(c,d) → False := by
    intro v hv1 hv2
    rw [Sym2.mem_iff] at hv1 hv2
    obtain ⟨hac, had, hbc, hbd⟩ := hdisj4
    rcases hv1 with rfl | rfl <;> rcases hv2 with h | h <;> simp_all
  have he1all : s(a,b) ∈ op1957_short_extendibility_hypothesis_is_necessary_allEdges :=
    (op1957_short_extendibility_hypothesis_is_necessary_allEdges_eq _).mpr (M.edgeSet_subset h1mem)
  have he2all : s(c,d) ∈ op1957_short_extendibility_hypothesis_is_necessary_allEdges :=
    (op1957_short_extendibility_hypothesis_is_necessary_allEdges_eq _).mpr (M.edgeSet_subset h2mem)
  obtain ⟨i, hi1, hi2⟩ :=
    op1957_short_extendibility_hypothesis_is_necessary_cover a b c d he1all he2all hdisj
  refine ⟨op1957_short_extendibility_hypothesis_is_necessary_pmSub i,
    op1957_short_extendibility_hypothesis_is_necessary_pmSub_perfect i, ?_, ?_⟩
  · intro v _
    exact Set.mem_univ v
  · intro x y hxy
    have hxy' : s(x,y) ∈ M.edgeSet := SimpleGraph.Subgraph.mem_edgeSet.mpr hxy
    rw [hset] at hxy'
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hxy'
    rcases hxy' with h | h
    · show s(x,y) ∈ op1957_short_extendibility_hypothesis_is_necessary_pme i
      rw [h]; exact hi1
    · show s(x,y) ∈ op1957_short_extendibility_hypothesis_is_necessary_pme i
      rw [h]; exact hi2

/-- The three-edge matching {0-3, 1-2, 8-9}. -/
def op1957_short_extendibility_hypothesis_is_necessary_M3 :
    op1957_replacement_counterexample_G.Subgraph :=
  op1957_short_extendibility_hypothesis_is_necessary_mk {0,1,2,3,8,9}
    {s(0,3), s(1,2), s(8,9)} (by decide) (by decide)

lemma op1957_short_extendibility_hypothesis_is_necessary_M3_matching :
    op1957_short_extendibility_hypothesis_is_necessary_M3.IsMatching := by
  show (op1957_short_extendibility_hypothesis_is_necessary_mk {0,1,2,3,8,9}
    {s(0,3), s(1,2), s(8,9)} (by decide) (by decide)).IsMatching
  unfold op1957_short_extendibility_hypothesis_is_necessary_mk SimpleGraph.Subgraph.IsMatching
  decide

lemma op1957_short_extendibility_hypothesis_is_necessary_M3_card :
    op1957_short_extendibility_hypothesis_is_necessary_M3.edgeSet.ncard = 3 := by
  show (op1957_short_extendibility_hypothesis_is_necessary_mk {0,1,2,3,8,9}
    {s(0,3), s(1,2), s(8,9)} (by decide) (by decide)).edgeSet.ncard = 3
  rw [op1957_short_extendibility_hypothesis_is_necessary_mk_ncard]
  decide

/-- A vertex outside {4,5,6} adjacent to a vertex of {4,5,6} must be 7. -/
lemma op1957_short_extendibility_hypothesis_is_necessary_step :
    ∀ v : Fin 10, v ∈ ({4,5,6} : Finset (Fin 10)) → ∀ x : Fin 10,
      op1957_replacement_counterexample_G.Adj v x → x ≠ 7 →
      x ∈ ({0,1,2,3,8,9} : Finset (Fin 10)) := by
  decide

/-- Each vertex of {0,1,2,3,8,9} has its partner in M3. -/
lemma op1957_short_extendibility_hypothesis_is_necessary_part_adj :
    ∀ x : Fin 10, x ∈ ({0,1,2,3,8,9} : Finset (Fin 10)) →
      op1957_short_extendibility_hypothesis_is_necessary_M3.Adj x (![3,2,1,0,0,0,0,0,9,8] x) := by
  show ∀ x : Fin 10, x ∈ ({0,1,2,3,8,9} : Finset (Fin 10)) →
    (op1957_short_extendibility_hypothesis_is_necessary_mk {0,1,2,3,8,9}
      {s(0,3), s(1,2), s(8,9)} (by decide) (by decide)).Adj x (![3,2,1,0,0,0,0,0,9,8] x)
  unfold op1957_short_extendibility_hypothesis_is_necessary_mk
  decide

/-- The partner map avoids {4,5,6}. -/
lemma op1957_short_extendibility_hypothesis_is_necessary_part_ne :
    ∀ v : Fin 10, v ∈ ({4,5,6} : Finset (Fin 10)) → ∀ x : Fin 10,
      x ∈ ({0,1,2,3,8,9} : Finset (Fin 10)) → (![3,2,1,0,0,0,0,0,9,8] x) ≠ v := by
  decide

lemma op1957_short_extendibility_hypothesis_is_necessary_not_three :
    ¬ is_k_extendable op1957_replacement_counterexample_G 3 := by
  unfold is_k_extendable
  intro h
  obtain ⟨-, -, h3⟩ := h
  obtain ⟨P, hP, hle⟩ := h3 op1957_short_extendibility_hypothesis_is_necessary_M3
    op1957_short_extendibility_hypothesis_is_necessary_M3_matching
    op1957_short_extendibility_hypothesis_is_necessary_M3_card
  have huniq : ∀ v : Fin 10, ∃! w, P.Adj v w :=
    SimpleGraph.Subgraph.isPerfectMatching_iff.mp hP
  have hmust : ∀ v : Fin 10, v ∈ ({4,5,6} : Finset (Fin 10)) → ∀ x : Fin 10,
      P.Adj v x → x = 7 := by
    intro v hv x hvx
    have hvx' : op1957_replacement_counterexample_G.Adj v x := P.adj_sub hvx
    by_contra hx
    have hxmem := op1957_short_extendibility_hypothesis_is_necessary_step v hv x hvx' hx
    have hadj : P.Adj x (![3,2,1,0,0,0,0,0,9,8] x) :=
      hle.2 (op1957_short_extendibility_hypothesis_is_necessary_part_adj x hxmem)
    have heq : v = ![3,2,1,0,0,0,0,0,9,8] x := (huniq x).unique hvx.symm hadj
    exact op1957_short_extendibility_hypothesis_is_necessary_part_ne v hv x hxmem heq.symm
  obtain ⟨w4, hw4, -⟩ := huniq 4
  obtain ⟨w5, hw5, -⟩ := huniq 5
  have h47 : P.Adj 4 7 := by
    have := hmust 4 (by decide) w4 hw4
    rw [this] at hw4
    exact hw4
  have h57 : P.Adj 5 7 := by
    have := hmust 5 (by decide) w5 hw5
    rw [this] at hw5
    exact hw5
  have h45 : (4 : Fin 10) = 5 := (huniq 7).unique h47.symm h57.symm
  exact absurd h45 (by decide)

lemma op1957_short_extendibility_hypothesis_is_necessary_matching_N :
    ∃ P : (op1957_replacement_counterexample_G.induce
      {v : Fin 10 | v ∈ Finset.univ.filter (fun v : Fin 10 => 7 ≤ v.val) ∧ v ≠ 7}).Subgraph,
      P.IsPerfectMatching := by
  set S : Set (Fin 10) :=
    {v : Fin 10 | v ∈ Finset.univ.filter (fun v : Fin 10 => 7 ≤ v.val) ∧ v ≠ 7} with hS
  have key : ∀ x : S, x = ⟨8, by decide⟩ ∨ x = ⟨9, by decide⟩ := by
    intro x
    have h1 : 7 ≤ (x : Fin 10).val := (Finset.mem_filter.mp x.property.1).2
    have h2 : (x : Fin 10).val ≠ 7 := fun hh => x.property.2 (Fin.ext hh)
    have h3 : (x : Fin 10).val ≤ 9 := by omega
    have h4 : (x : Fin 10).val = 8 ∨ (x : Fin 10).val = 9 := by omega
    rcases h4 with h | h
    · left; exact Subtype.ext (Fin.ext h)
    · right; exact Subtype.ext (Fin.ext h)
  have h89 : (op1957_replacement_counterexample_G.induce S).Adj ⟨8, by decide⟩ ⟨9, by decide⟩ := by
    rw [SimpleGraph.induce_adj]; decide
  refine ⟨⊤, ?_⟩
  rw [SimpleGraph.Subgraph.isPerfectMatching_iff]
  intro v
  rcases key v with hv | hv
  · subst hv
    refine ⟨⟨9, by decide⟩, h89, ?_⟩
    intro y hy
    rcases key y with hy' | hy'
    · subst hy'
      exact absurd hy (fun hh => op1957_replacement_counterexample_G.irrefl
        (SimpleGraph.induce_adj.mp (SimpleGraph.Subgraph.top_adj.mp hh)))
    · subst hy'; rfl
  · subst hv
    refine ⟨⟨8, by decide⟩, h89.symm, ?_⟩
    intro y hy
    rcases key y with hy' | hy'
    · subst hy'; rfl
    · subst hy'
      exact absurd hy (fun hh => op1957_replacement_counterexample_G.irrefl
        (SimpleGraph.induce_adj.mp (SimpleGraph.Subgraph.top_adj.mp hh)))

theorem op1957_short_extendibility_hypothesis_is_necessary :
    let T : Finset (Fin 10) := Finset.univ.filter (fun v => v.val < 3)
    let N : Finset (Fin 10) := Finset.univ.filter (fun v => 7 ≤ v.val)
    is_k_extendable op1957_replacement_counterexample_G 2 ∧
    ¬ is_k_extendable op1957_replacement_counterexample_G 3 ∧
    op1957_replacement_counterexample_G.Connected ∧
    T.card = 3 ∧ N.card = 3 ∧ Disjoint T N ∧
    (∀ a ∈ T, ∀ b ∈ T, a ≠ b → op1957_replacement_counterexample_G.Adj a b) ∧
    (∀ a ∈ T, ∀ b ∈ N, ¬ op1957_replacement_counterexample_G.Adj a b) ∧
    (∀ a ∈ T, ∀ b, b ∉ T → b ∉ N → op1957_replacement_counterexample_G.Adj a b) ∧
    (∃ P : (op1957_replacement_counterexample_G.induce {v | v ∈ N ∧ v ≠ 7}).Subgraph, P.IsPerfectMatching) ∧
    (op1957_replacement_counterexample_G.induce {v | v ∉ T ∧ v ∉ N}).Connected := by
  refine ⟨op1957_short_extendibility_hypothesis_is_necessary_two,
    op1957_short_extendibility_hypothesis_is_necessary_not_three,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    op1957_short_extendibility_hypothesis_is_necessary_matching_N, by decide⟩
